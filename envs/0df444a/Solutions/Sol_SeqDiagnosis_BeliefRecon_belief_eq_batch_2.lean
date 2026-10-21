-- Prove2me | solution 2 for SeqDiagnosis.BeliefRecon.belief_eq_batch
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T14:52:04.346804+00:00
-- url     : https://prove2.me/submissions/beccf0cd-b36c-4d1d-b090-a667dc3065c7

import Mathlib
import Definitions.Def_SeqDiagnosis_BeliefRecon_Bayes

set_option autoImplicit false
open SeqDiagnosis.BeliefRecon

private theorem bayes_simplex {Y : Type*} {N : ℕ}
    (f : Fin (N + 1) → Y → ℝ) (hf : ∀ i y, 0 < f i y)
    (y : Y) (q : Fin (N + 1) → ℝ) (hq : q ∈ stdSimplex ℝ (Fin (N + 1))) :
    0 < ∑ i, q i * f i y ∧ bayes f q y ∈ stdSimplex ℝ (Fin (N + 1)) := by
  obtain ⟨hq0, hq1⟩ := hq
  have hD : 0 < ∑ i, q i * f i y := by
    obtain ⟨k, hk⟩ : ∃ k, 0 < q k := by
      by_contra h
      push_neg at h
      have : ∑ i, q i = 0 := Finset.sum_eq_zero fun i _ => le_antisymm (h i) (hq0 i)
      rw [this] at hq1; exact zero_ne_one hq1
    exact Finset.sum_pos' (fun i _ => mul_nonneg (hq0 i) (hf i y).le)
      ⟨k, Finset.mem_univ _, mul_pos hk (hf k y)⟩
  refine ⟨hD, fun j => ?_, ?_⟩
  · exact div_nonneg (mul_nonneg (hq0 j) (hf j y).le) hD.le
  · simp only [bayes]
    rw [← Finset.sum_div, div_self hD.ne']

private theorem batch {Y : Type*} {N : ℕ}
    (f : Fin (N + 1) → Y → ℝ) (hf : ∀ i y, 0 < f i y)
    (ys : List Y) : ∀ (q : Fin (N + 1) → ℝ), q ∈ stdSimplex ℝ (Fin (N + 1)) → ∀ j,
    belief f q ys j = q j * (ys.map (f j)).prod / ∑ i, q i * (ys.map (f i)).prod := by
  induction ys with
  | nil => 
    intro q hq j
    simp [belief, hq.2]
  | cons y ys ih =>
    intro q hq j
    obtain ⟨hD, hq'⟩ := bayes_simplex f hf y q hq
    have h1 : belief f q (y :: ys) = belief f (bayes f q y) ys := rfl
    rw [h1, ih _ hq' j]
    simp only [bayes, List.map_cons, List.prod_cons]
    have e1 : ∀ i, q i * f i y / (∑ i, q i * f i y) * ((ys.map (f i)).prod)
        = (q i * (f i y * (ys.map (f i)).prod)) / (∑ i, q i * f i y) := by
      intro i; field_simp
    simp only [e1, ← Finset.sum_div]
    rw [div_div_div_cancel_right₀ hD.ne']

theorem solution {Y : Type*} {N : ℕ}
    (f : Fin (N + 1) → Y → ℝ) (hf : ∀ i y, 0 < f i y)
    (θ : Fin (N + 1) → ℝ) (hθ : θ ∈ stdSimplex ℝ (Fin (N + 1)))
    (ys : List Y) (j : Fin (N + 1)) :
    belief f θ ys j = θ j * (ys.map (f j)).prod /
      ∑ i, θ i * (ys.map (f i)).prod :=
  batch f hf ys θ hθ j
