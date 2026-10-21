-- Prove2me | solution 1 for SeqDiagnosis.BeliefRecon.belief_eq_batch
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T09:57:32.692395+00:00
-- url     : https://prove2.me/submissions/4e43b6ba-eb4f-41a9-8dc5-af8876077001

import Mathlib
import Definitions.Def_SeqDiagnosis_BeliefRecon_Bayes

open SeqDiagnosis.BeliefRecon

theorem solution {Y : Type*} {N : ℕ}
    (f : Fin (N + 1) → Y → ℝ) (hf : ∀ i y, 0 < f i y)
    (θ : Fin (N + 1) → ℝ) (hθ : θ ∈ stdSimplex ℝ (Fin (N + 1)))
    (ys : List Y) (j : Fin (N + 1)) :
    belief f θ ys j = θ j * (ys.map (f j)).prod /
      ∑ i, θ i * (ys.map (f i)).prod := by
  have key : ∀ (ys : List Y) (q : Fin (N + 1) → ℝ), q ∈ stdSimplex ℝ (Fin (N + 1)) →
      ∀ j, belief f q ys j = q j * (ys.map (f j)).prod / ∑ i, q i * (ys.map (f i)).prod := by
    intro ys
    induction ys with
    | nil =>
      intro q hq j
      obtain ⟨_, hq1⟩ := hq
      simp [belief, hq1]
    | cons y ys ih =>
      intro q hq j
      obtain ⟨hq0, hq1⟩ := hq
      have hpos : 0 < ∑ i, q i * f i y := by
        obtain ⟨k, hk⟩ : ∃ k, 0 < q k := by
          by_contra h
          push Not at h
          have : ∑ i, q i ≤ 0 := Finset.sum_nonpos (fun i _ => h i)
          linarith
        calc (0:ℝ) < q k * f k y := mul_pos hk (hf k y)
          _ ≤ ∑ i, q i * f i y :=
            Finset.single_le_sum (f := fun i => q i * f i y)
              (fun i _ => mul_nonneg (hq0 i) (hf i y).le) (Finset.mem_univ k)
      have hsimp : bayes f q y ∈ stdSimplex ℝ (Fin (N + 1)) := by
        refine ⟨fun i => div_nonneg (mul_nonneg (hq0 i) (hf i y).le) hpos.le, ?_⟩
        simp only [bayes]
        rw [← Finset.sum_div]
        exact div_self hpos.ne'
      have hstep : belief f q (y :: ys) = belief f (bayes f q y) ys := rfl
      rw [hstep, ih _ hsimp j]
      simp only [bayes, List.map_cons, List.prod_cons]
      set D := ∑ i, q i * f i y
      have : ∑ i, q i * f i y / D * (ys.map (f i)).prod =
          (∑ i, q i * (f i y * (ys.map (f i)).prod)) / D := by
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        ring
      rw [this, div_mul_eq_mul_div, div_div_div_cancel_right₀ hpos.ne']
      ring_nf
  exact key ys θ hθ j
