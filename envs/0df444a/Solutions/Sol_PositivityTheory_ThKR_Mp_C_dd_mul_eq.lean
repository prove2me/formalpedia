-- Prove2me | solution 1 for PositivityTheory.ThKR.Mp.C.dd_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:41:19.224347+00:00
-- url     : https://prove2.me/submissions/e43c53cf-b903-46aa-9efa-9c671e6514cb

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_ContinuousPair
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_MapOfRealMul
import Theorems.Thm_PositivityTheory_ThKR_Mp_C_upperPart_mul
import Theorems.Thm_PositivityTheory_ThKR_Mp_C_map_ofReal_mul
import Theorems.Thm_PositivityTheory_ThKR_Mp_C_det_map_ofReal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil PositivityTheory.ThKF.E Filter Topology PositivityTheory.ThKR.LL
open scoped Real
open PositivityTheory PositivityTheory.ThKR PositivityTheory.ThKR.Mp
variable {l : Type} [Fintype l] [DecidableEq l]
open PositivityTheory.ThKR.Mp.C
namespace PositivityTheory.ThKR.Mp.C
theorem _root_.solution (s s' : Mat l) (hd : s.toBlocks₁₁.det ≠ 0) :
    dd (s * s') = (s.toBlocks₁₁.det : ℂ) *
      (upperParabolic s' + (s.toBlocks₁₁⁻¹ * s.toBlocks₁₂).map Complex.ofReal * loQ s').det := by
  have hu : IsUnit s.toBlocks₁₁.det := isUnit_iff_ne_zero.2 hd
  have hAS : s.toBlocks₁₁ * (s.toBlocks₁₁⁻¹ * s.toBlocks₁₂) = s.toBlocks₁₂ := by
    rw [← Matrix.mul_assoc, mul_nonsing_inv _ hu, Matrix.one_mul]
  have hB : s.toBlocks₁₂.map Complex.ofReal =
      s.toBlocks₁₁.map Complex.ofReal * (s.toBlocks₁₁⁻¹ * s.toBlocks₁₂).map Complex.ofReal := by
    rw [← map_ofReal_mul, hAS]
  rw [dd, upperPart_mul, hB, Matrix.mul_assoc, ← Matrix.mul_add, det_mul, det_map_ofReal]
end PositivityTheory.ThKR.Mp.C
