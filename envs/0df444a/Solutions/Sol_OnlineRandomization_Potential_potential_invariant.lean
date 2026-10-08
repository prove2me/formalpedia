-- Prove2me | solution 1 for OnlineRandomization.Potential.potential_invariant
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T00:31:54.215609+00:00
-- url     : https://prove2.me/submissions/75c8d3e1-d5ea-43d7-8e26-98dfb87b688d

import Mathlib
import Definitions.Def_OnlineRandomization_Potential_AugPotential

open OnlineRandomization.Potential in
theorem PI02052ca9.answers_append {R A : Type*} (G : DetAlg R A) (r : List R) (x : R) :
    G.answers (r ++ [x]) = G.answers r ++ [G (r ++ [x])] := by
  unfold DetAlg.answers
  rw [List.length_append, List.length_singleton, List.range_succ, List.map_append,
    List.map_singleton]
  congr 1
  · apply List.map_congr_left
    intro i hi
    rw [List.mem_range] at hi
    rw [List.take_append_of_le_length (by omega)]
  · rw [List.take_of_length_le (by simp)]

open OnlineRandomization.Potential MeasureTheory in
theorem solution {R A Ω : Type*} [Fintype A] [MeasurableSpace Ω]
    (F : Game R A) (α : ℝ → ℝ) (g : BehAlg R A) (Φ : List R → List A → List A → ℝ)
    (hΦ : IsAugPotential F α g Φ) (H : RandAlg R A Ω) (M : DetAlg R A)
    (hM : ObeysPotentialRule Φ H M) (r : List R) :
    0 ≤ ∫ y, Φ r (M.answers r) ((H.alg y).answers r) ∂H.μ := by
  induction r using List.reverseRecOn with
  | nil =>
    have h0 : ∀ G : DetAlg R A, G.answers [] = [] := fun G => rfl
    simp only [h0, hΦ.zero, integral_zero, le_refl]
  | append_singleton r x ih =>
    refine le_trans ih (le_of_le_of_eq (hM r x) ?_)
    simp only [PI02052ca9.answers_append]
