-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.E2.P.Fdata.mul_le_weighted_squares
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:32:48.844965+00:00
-- url     : https://prove2.me/submissions/942f8ab9-a16f-496c-adaa-fa7e5c5b3d9f

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_EigenvalueSeparation_AlmostEverywhereEigen_OneStepOf
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_EigenvalueSeparation_AlmostEverywhereEigen_PositiveMeasureNorms_MulLeWeightedSquares

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal ComplexConjugate
open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E2 PositivityTheory.Rg.BcB.E2.P
open PositivityTheory.Rg.BcB.E2.P.Fdata
namespace PositivityTheory.Rg.BcB.E2.P.Fdata
theorem _root_.solution (a b W : ℝ≥0∞) (h0 : W ≠ 0) (ht : W ≠ ⊤) : a * b ≤ W⁻¹ * a ^ 2 + W * b ^ 2 := by
  rcases le_or_gt a (W * b) with h | h
  · calc a * b ≤ W * b * b := by gcongr
      _ = W * b ^ 2 := by rw [pow_two, mul_assoc]
      _ ≤ _ := le_add_self
  · have hb : b ≤ W⁻¹ * a := by
      calc b = W⁻¹ * (W * b) := by rw [← mul_assoc, ENNReal.inv_mul_cancel h0 ht, one_mul]
        _ ≤ W⁻¹ * a := by gcongr
    calc a * b ≤ a * (W⁻¹ * a) := by gcongr
      _ = W⁻¹ * a ^ 2 := by ring
      _ ≤ _ := le_self_add
end PositivityTheory.Rg.BcB.E2.P.Fdata
