-- Prove2me | solution 1 for PositivityTheory.ThKR.Mp.C.sec_apply_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:30:38.462745+00:00
-- url     : https://prove2.me/submissions/b6e13d5e-1122-439e-8d0f-bee590f530fd

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_ContinuousPair
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaplecticDerivatives_MapOfRealMul
import Theorems.Thm_PositivityTheory_ThKR_LL_dil_apply
import Theorems.Thm_PositivityTheory_ThKR_LL_ph_apply


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
theorem _root_.solution (s : Mat l) (hA : IsUnit (bl Sum.inl Sum.inl s)) (f : Sch l) :
    sec s f 0 = (((√|s.toBlocks₁₁.det|)⁻¹ : ℝ) : ℂ) *
      fou l (ph (-(Ring.inverse (bl Sum.inl Sum.inl s) * bl Sum.inl Sum.inr s)) (fouInv l f)) 0 := by
  simp only [sec, big, ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply, SchwartzMap.smul_apply, ph_apply,
    dil_apply hA.ringInverse, map_zero, inner_zero_left, mul_zero, ofReal_zero, zero_mul, Complex.exp_zero, one_mul,
    smul_eq_mul]
end PositivityTheory.ThKR.Mp.C
