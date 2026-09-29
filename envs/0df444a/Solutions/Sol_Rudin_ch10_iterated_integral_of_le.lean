-- Prove2me | solution 1 for Rudin.ch10_iterated_integral_of_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-14T05:16:47.017746+00:00
-- url     : https://prove2.me/submissions/b0d4741a-1bbc-446a-be31-83ed08f73330

import Mathlib
import Definitions.Def_Rudin_ch10_forms

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace RudinFix10

open Filter Topology MeasureTheory

theorem ch10_iterated_integral (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d) (f : ℝ → ℝ → ℝ)
    (hf : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2) (Set.Icc a b ×ˢ Set.Icc c d)) :
    (∫ x in a..b, ∫ y in c..d, f x y) = ∫ y in c..d, ∫ x in a..b, f x y := by
  refine MeasureTheory.intervalIntegral_intervalIntegral_swap ?_
  rw [Set.uIoc_of_le hab, Set.uIoc_of_le hcd]
  exact (hf.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
    (Set.prod_mono Set.Ioc_subset_Icc_self Set.Ioc_subset_Icc_self)

end RudinFix10

open Filter Topology MeasureTheory in
theorem solution (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d) (f : ℝ → ℝ → ℝ)
    (hf : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2) (Set.Icc a b ×ˢ Set.Icc c d)) :
    (∫ x in a..b, ∫ y in c..d, f x y) = ∫ y in c..d, ∫ x in a..b, f x y :=
  RudinFix10.ch10_iterated_integral a b c d hab hcd f hf
