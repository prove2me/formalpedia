-- Prove2me | solution 1 for PolyClinch.TwoSided.lemma_3_7
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-02T04:22:52.1731+00:00
-- url     : https://prove2.me/submissions/f01ba96a-57b9-44ce-817f-b7da5bd8497e

import Mathlib
import Definitions.Def_PolyClinch_TwoSided_Clinching

open PolyClinch.TwoSided Finset

theorem solution {n m : ℕ} (E : Finset (Fin n × Fin m)) (ε : ℝ) (hε : 0 < ε)
    (I : PublicInfo E) (hI : Valid E ε I) (A : Allocation E) (hA : Mech2Outcome E I ε A) :
    ∑ i, A.p i = ∑ j, A.r j := by
  -- one clinch keeps `∑ p = ∑ (old p) + ∑ dr`
  have hclinch : ∀ (c : Fin (n + m) → ℝ) (i : Fin (n + m)) (u u' : Alg2Inner E),
      Alg2Clinch E I c i u u' →
      ∑ k, u'.p k - ∑ j, u'.dr j = ∑ k, u.p k - ∑ j, u.dr j := by
    intro c i u u' ⟨ξ, hmax, _, hp, _, hdr⟩
    have hzero : ∀ e ∉ extEdgesOfBuyer E i, ξ e = 0 := hmax.1.2.1
    have h1 : ∑ k, u'.p k = ∑ k, u.p k + c i * ∑ e ∈ extEdgesOfBuyer E i, ξ e := by
      rw [hp, Finset.sum_update_of_mem (Finset.mem_univ _),
        Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ i) u.p]
      ring
    have h2 : ∑ j, u'.dr j = ∑ j, u.dr j + c i * ∑ e ∈ extEdgesOfBuyer E i, ξ e := by
      rw [hdr, Finset.sum_add_distrib]
      congr 1
      have hf : ∑ j, ∑ e ∈ extEdgesOfSeller E j, c e.1.1 * ξ e = ∑ e, c e.1.1 * ξ e := by
        unfold extEdgesOfSeller
        exact Finset.sum_fiberwise _ _ _
      rw [hf, Finset.mul_sum]
      rw [← Finset.sum_subset (Finset.subset_univ (extEdgesOfBuyer E i))]
      · apply Finset.sum_congr rfl
        intro e he
        unfold extEdgesOfBuyer at he
        rw [(Finset.mem_filter.1 he).2]
      · intro e _ he
        rw [hzero e he, mul_zero]
    rw [h1, h2]; ring
  have hstep : ∀ s s' : Alg2State E, Alg2Step E I ε s s' →
      ∑ k, s.p k = ∑ j, s.r j → ∑ k, s'.p k = ∑ j, s'.r j := by
    intro s s' ⟨u, hu0, hcl, _, hp, hr, _⟩ hs
    have : ∀ k ≤ n + m, ∑ q, (u k).p q - ∑ j, (u k).dr j = ∑ q, s.p q := by
      intro k
      induction k with
      | zero => intro _; rw [hu0]; simp
      | succ k ih =>
        intro hk
        rw [hclinch _ _ _ _ (hcl k (by omega)), ih (by omega)]
    have h := this (n + m) le_rfl
    rw [hp, hr]
    simp only [Pi.add_apply]
    rw [Finset.sum_add_distrib, ← hs]
    linarith
  obtain ⟨S, ⟨T, s, hinit, hrun, _, rfl⟩, rfl⟩ := hA
  have hinv : ∀ t ≤ T, ∑ k, (s t).p k = ∑ j, (s t).r j := by
    intro t
    induction t with
    | zero =>
      intro _
      obtain ⟨_, hp, hr, _⟩ := hinit
      rw [hp, hr]; simp
    | succ t ih =>
      intro ht
      exact hstep _ _ (hrun t (by omega)).2 (ih (by omega))
  have h := hinv T le_rfl
  simp only [toOriginal, Finset.sum_sub_distrib]
  rw [Fin.sum_univ_add] at h
  linarith
