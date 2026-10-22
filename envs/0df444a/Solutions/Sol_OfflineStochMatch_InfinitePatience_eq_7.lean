-- Prove2me | solution 1 for OfflineStochMatch.InfinitePatience.eq_7
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:20:48.156685+00:00
-- url     : https://prove2.me/submissions/e1de39d1-227e-4290-8f4e-e3dc027554ea

import Mathlib
import Definitions.Def_OfflineStochMatch_InfinitePatience_Setting
set_option autoImplicit false

open OfflineStochMatch.InfinitePatience

lemma oo_coin_nonneg {ι : Type*} [Fintype ι] (q : ι → ℝ) (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1)
    (c : ι → Bool) : 0 ≤ coinWeight q c := by
  unfold coinWeight
  apply Finset.prod_nonneg
  intro i _
  unfold bern
  split_ifs
  · exact (hq i).1
  · linarith [(hq i).2]

lemma oo_matched {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E) (t : V → ℕ∞) (Y A P : E → Bool)
    (L : List E) :
    ∀ (st : RunState V) (v : V), v ∈ (L.foldl (step G t Y A P) st).matched →
      v ∈ st.matched ∨ ∃ f ∈ L, v ∈ G.ends f ∧ A f = true ∧ P f = true ∧ Y f = true := by
  induction L with
  | nil => intro st v h; exact Or.inl h
  | cons f L ih =>
    intro st v h
    rw [List.foldl_cons] at h
    rcases ih _ v h with h1 | ⟨f', hf', h2⟩
    · unfold step at h1
      by_cases hc : CanProbe G t st f ∧ Y f = true ∧ A f = true
      · by_cases hp : P f = true
        · simp only [if_pos hc, hp, if_true, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
            true_and] at h1
          rcases h1 with h3 | h3
          · exact Or.inl h3
          · right
            exact ⟨f, List.mem_cons_self, h3, hc.2.2, hp, hc.2.1⟩
        · simp only [if_pos hc, hp, if_false] at h1
          exact Or.inl h1
      · simp only [if_neg hc] at h1
        exact Or.inl h1
    · exact Or.inr ⟨f', List.mem_cons_of_mem _ hf', h2⟩

lemma oo_safe_free {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E) (t : V → ℕ∞) (σ : E ≃ Fin (Fintype.card E))
    (Y A P : E → Bool) (e : E) (h : IsSafe G t σ Y A P e) : IsFree G t σ Y A P e := by
  intro v hv
  refine ⟨?_, ?_⟩
  · intro hm
    unfold stateBefore at hm
    rcases oo_matched G t Y A P _ _ v hm with h1 | ⟨f, hf, hvf, hA, hP, hY⟩
    · simp [initState] at h1
    · rw [List.mem_map] at hf
      obtain ⟨i, hi, rfl⟩ := hf
      rw [List.mem_filter] at hi
      have hlt : i < σ e := by simpa using hi.2
      have hne : σ.symm i ≠ e := by
        intro hh
        have : σ e = i := by rw [← hh]; exact σ.apply_symm_apply i
        rw [this] at hlt
        exact lt_irrefl _ hlt
      refine h.2 (σ.symm i) hne ⟨v, hv, hvf⟩ ?_ ⟨hA, hP, hY⟩
      simpa using hlt
  · have := h.1 v hv
    have hfin : (((stateBefore G t σ Y A P e).probes v : ℕ) : ℕ∞) ≠ ⊤ := ENat.coe_ne_top _
    exact (ENat.add_one_le_iff hfin).1 this

lemma oo_prob_mono {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (p y : E → ℝ) (a : ℝ → ℝ) (hp : ∀ f, 0 ≤ p f ∧ p f ≤ 1) (hy : ∀ f, 0 ≤ y f ∧ y f ≤ 1)
    (ha : ∀ f, 0 ≤ a (p f * y f) ∧ a (p f * y f) ≤ 1)
    (ev1 ev2 : (E ≃ Fin (Fintype.card E)) → (E → Bool) → (E → Bool) → (E → Bool) → Prop)
    (h : ∀ σ Y A P, ev1 σ Y A P → ev2 σ Y A P) :
    prob p y a ev1 ≤ prob p y a ev2 := by
  unfold prob
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum; intro σ _
  apply Finset.sum_le_sum; intro Y _
  apply Finset.sum_le_sum; intro A _
  apply Finset.sum_le_sum; intro P _
  have h0 : 0 ≤ coinWeight y Y * coinWeight (fun f => a (p f * y f)) A * coinWeight p P :=
    mul_nonneg (mul_nonneg (oo_coin_nonneg y hy Y) (oo_coin_nonneg (fun f => a (p f * y f)) ha A)) (oo_coin_nonneg p hp P)
  apply mul_le_mul_of_nonneg_left _ h0
  classical
  by_cases h1 : ev1 σ Y A P
  · rw [if_pos h1, if_pos (h σ Y A P h1)]
  · rw [if_neg h1]; split_ifs <;> norm_num

theorem solution {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E) (p y : E → ℝ) (t : V → ℕ∞) (aT : ℝ → ℝ)
    (hp : ∀ f, 0 ≤ p f ∧ p f ≤ 1) (hy : LPFeasible G p t y)
    (haT : ∀ z ∈ Set.Icc (0 : ℝ) 1, aT z ∈ Set.Icc (0 : ℝ) 1) (e : E) :
    aT (p e * y e) * probSafe G p t y aT e ≤ aT (p e * y e) * probFree G p t y aT e := by
  have hy' : ∀ f, 0 ≤ y f ∧ y f ≤ 1 := hy.1
  have hz : ∀ f, p f * y f ∈ Set.Icc (0 : ℝ) 1 := fun f =>
    ⟨mul_nonneg (hp f).1 (hy' f).1, by nlinarith [(hp f).1, (hp f).2, (hy' f).1, (hy' f).2]⟩
  have ha : ∀ f, 0 ≤ aT (p f * y f) ∧ aT (p f * y f) ≤ 1 := fun f => haT _ (hz f)
  apply mul_le_mul_of_nonneg_left _ (ha e).1
  exact oo_prob_mono (V := V) (E := E) p y aT hp hy' ha _ _ (fun σ Y A P h => oo_safe_free G t σ Y A P e h)
