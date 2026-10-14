-- Prove2me | solution 1 for RobustMNL.Static.largest_optimal_robust
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T02:59:18.458914+00:00
-- url     : https://prove2.me/submissions/4aa43e2a-d336-40c8-bd40-466afdebfef0

import Mathlib
import Theorems.Thm_RobustMNL_Static_revenue_ordered_robust
import Definitions.Def_RobustMNL_Static_Model

open scoped BigOperators
open RobustMNL.Static

private lemma rm_den {n : ℕ} (p : ℝ × (Fin n → ℝ)) (hp : IsPos p)
    (S : Finset (Fin n)) : 0 < (∑ i ∈ S, p.2 i) + p.1 := by
  exact add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun i _ => (hp.2 i).le) hp.1

private lemma rm_cont {n : ℕ} (r : Fin n → ℝ) (V : Set (ℝ × (Fin n → ℝ)))
    (hp : ∀ p ∈ V, IsPos p) (S : Finset (Fin n)) : ContinuousOn (rev r S) V := by
  unfold rev ChoiceCDLP.MNL.mnlObjective
  apply ContinuousOn.div
  · fun_prop
  · fun_prop
  · intro p h
    exact ne_of_gt (rm_den p (hp p h) S)

private lemma rm_min {n : ℕ} (r : Fin n → ℝ) (V : Set (ℝ × (Fin n → ℝ)))
    (hc : IsCompact V) (hn : V.Nonempty) (hp : ∀ p ∈ V, IsPos p) (S : Finset (Fin n)) :
    ∃ p ∈ V, worst V r S = rev r S p ∧ ∀ q ∈ V, rev r S p ≤ rev r S q := by
  exact hc.exists_sInf_image_eq_and_le hn (rm_cont r V hp S)

private lemma rm_low {n : ℕ} (r : Fin n → ℝ) (V : Set (ℝ × (Fin n → ℝ)))
    (hc : IsCompact V) (hn : V.Nonempty) (hp : ∀ p ∈ V, IsPos p) (S : Finset (Fin n))
    (q : ℝ × (Fin n → ℝ)) (hq : q ∈ V) : worst V r S ≤ rev r S q := by
  obtain ⟨p, _, he, hl⟩ := rm_min r V hc hn hp S
  rw [he]
  exact hl q hq

private lemma rm_le_worst {n : ℕ} (r : Fin n → ℝ) (V : Set (ℝ × (Fin n → ℝ)))
    (hc : IsCompact V) (hn : V.Nonempty) (hp : ∀ p ∈ V, IsPos p) (S : Finset (Fin n))
    (z : ℝ) (hz : ∀ q ∈ V, z ≤ rev r S q) : z ≤ worst V r S := by
  obtain ⟨p, hm, he, _⟩ := rm_min r V hc hn hp S
  rw [he]
  exact hz p hm

private lemma rm_max {n : ℕ} (r : Fin n → ℝ) (V : Set (ℝ × (Fin n → ℝ)))
    (S : Finset (Fin n)) : worst V r S ≤ Zstar V r := by
  exact Finset.le_sup' (worst V r) (Finset.mem_univ S)

private lemma rm_exists {n : ℕ} (r : Fin n → ℝ) (V : Set (ℝ × (Fin n → ℝ))) :
    ∃ S, IsSmallestOptimal V r S := by
  classical
  obtain ⟨S, _, he⟩ := Finset.exists_mem_eq_sup'
    (s := (Finset.univ : Finset (Finset (Fin n)))) Finset.univ_nonempty (worst V r)
  have hs : worst V r S = Zstar V r := he.symm
  let opts := (Finset.univ : Finset (Finset (Fin n))).filter (fun T => worst V r T = Zstar V r)
  have ho : opts.Nonempty := ⟨S, by simp [opts, hs]⟩
  obtain ⟨T, ht, hmin⟩ := opts.exists_min_image Finset.card ho
  refine ⟨T, (Finset.mem_filter.mp ht).2, ?_⟩
  intro U hu
  exact hmin U (by simp [opts, hu])

private lemma rm_mul {n : ℕ} (r : Fin n → ℝ) (p : ℝ × (Fin n → ℝ))
    (hp : IsPos p) (S : Finset (Fin n)) :
    rev r S p * ((∑ i ∈ S, p.2 i) + p.1) = ∑ i ∈ S, r i * p.2 i := by
  exact div_mul_cancel₀ _ (ne_of_gt (rm_den p hp S))

private lemma rm_insert_mul {n : ℕ} (r : Fin n → ℝ) (p : ℝ × (Fin n → ℝ))
    (hp : IsPos p) (S : Finset (Fin n)) (i : Fin n) (hi : i ∉ S) :
    rev r (insert i S) p * (p.2 i + (∑ j ∈ S, p.2 j) + p.1) =
      r i * p.2 i + rev r S p * ((∑ j ∈ S, p.2 j) + p.1) := by
  simpa [Finset.sum_insert hi, rm_mul r p hp S] using rm_mul r p hp (insert i S)


 theorem solution {n : ℕ} (r : Fin n → ℝ) (V : Set (ℝ × (Fin n → ℝ)))
    (hV : IsCompact V) (hne : V.Nonempty) (hpos : ∀ p ∈ V, IsPos p) (S : Finset (Fin n))
    (hS : IsSmallestOptimal V r S) (i : Fin n) :
    i ∈ S ↔ ∃ p ∈ V, ∃ T : Finset (Fin n), IsSmallestOptimal {p} r T ∧ i ∈ T := by
  classical
  have hchar := (RobustMNL.Static.revenue_ordered_robust r V hV hne hpos S).mp hS
  constructor
  · intro hi
    obtain ⟨p, hp, he, _⟩ := rm_min r V hV hne hpos S
    have hp' := hpos p hp
    have hv : rev r S p = Zstar V r := he.symm.trans hS.1
    have hz : Zstar {p} r = Zstar V r := by
      apply le_antisymm
      · apply Finset.sup'_le
        intro T _
        simp only [worst, Set.image_singleton, csInf_singleton]
        have hsum : (∑ j ∈ T, (r j - Zstar V r) * p.2 j) ≤
            ∑ j ∈ S, (r j - Zstar V r) * p.2 j := by
          have hind (A : Finset (Fin n)) :
              (∑ j : Fin n, if j ∈ A then (r j - Zstar V r) * p.2 j else 0) =
                ∑ j ∈ A, (r j - Zstar V r) * p.2 j := by
            rw [← Finset.sum_filter]
            simp
          rw [← hind T, ← hind S]
          apply Finset.sum_le_sum
          intro j _
          have hj : j ∈ S ↔ Zstar V r < r j := by simp [hchar]
          by_cases hs : j ∈ S <;> by_cases ht : j ∈ T <;> simp only [hs, ht, if_true, if_false] <;> try exact le_rfl
          · exact mul_nonneg (sub_nonneg.mpr (hj.mp hs).le) (hp'.2 j).le
          · exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (le_of_not_gt (fun h => hs (hj.mpr h)))) (hp'.2 j).le
        simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
        have hSval := rm_mul r p hp' S
        rw [hv] at hSval
        have hTval := rm_mul r p hp' T
        have hd := rm_den p hp' T
        nlinarith
      · have hx := rm_max r ({p} : Set (ℝ × (Fin n → ℝ))) S
        simpa [worst, hv] using hx
    refine ⟨p, hp, S, ?_, hi⟩
    apply (RobustMNL.Static.revenue_ordered_robust r {p} isCompact_singleton
      (Set.singleton_nonempty p) (by intro q hq; rcases Set.mem_singleton_iff.mp hq with rfl; exact hp') S).mpr
    simpa [hz] using hchar
  · rintro ⟨p, hp, T, hT, hi⟩
    have hp' := hpos p hp
    have hnpos : ∀ q ∈ ({p} : Set (ℝ × (Fin n → ℝ))), IsPos q := by
      intro q hq
      rcases Set.mem_singleton_iff.mp hq with rfl
      exact hp'
    have hTchar := (RobustMNL.Static.revenue_ordered_robust r {p} isCompact_singleton
      (Set.singleton_nonempty p) hnpos T).mp hT
    have hz : Zstar V r ≤ Zstar {p} r := by
      apply Finset.sup'_le
      intro A _
      have ha := rm_max r ({p} : Set (ℝ × (Fin n → ℝ))) A
      simp only [worst, Set.image_singleton, csInf_singleton] at ha
      exact (rm_low r V hV hne hpos A p hp).trans ha
    rw [hTchar] at hi
    rw [hchar]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact hz.trans_lt hi
#print axioms solution
