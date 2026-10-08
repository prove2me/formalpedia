-- Prove2me | solution 1 for SubstOverbooking.Structure.mean_additive
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T07:20:13.772322+00:00
-- url     : https://prove2.me/submissions/4b0b69f3-08aa-4abc-b415-6ab56607ce8b

import Mathlib
import Definitions.Def_SubstOverbooking_Structure_Setting

open SubstOverbooking.Structure MeasureTheory

theorem solution (P : Set ℝ) (L : ℝ → PMF ℕ) (hL : IsSemigroupFamily P L)
    (u s : ℝ) (hu : u ∈ P) (hs : s ∈ P) :
    ∫ k, (k : ℝ) ∂(L (u + s)).toMeasure =
      ∫ k, (k : ℝ) ∂(L u).toMeasure + ∫ k, (k : ℝ) ∂(L s).toMeasure := by
  rw [hL.1 u hu s hs]
  rw [integral_map (by fun_prop) (by fun_prop)]
  simp only [Nat.cast_add]
  rw [integral_add ((hL.2 u hu).comp_fst (L s).toMeasure)
    ((hL.2 s hs).comp_snd (L u).toMeasure)]
  rw [integral_fun_fst, integral_fun_snd]
  simp

#print axioms solution
