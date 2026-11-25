-- Prove2me | solution 1 for PositivityTheory.ThKG.Loc.Bump.FT_gm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:09:06.622062+00:00
-- url     : https://prove2.me/submissions/e85cf275-148b-4ce3-8163-e71cb2bea801

import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_ExistsDensity
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianComplexFourier
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_IntegrableConjPowGaussian
import Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_ch_sum
import Theorems.Thm_GroundTheory_Global_complexFourier_conj_pow_mul_gaussian
import Theorems.Thm_P2M_GroundTheory_Global_traceForm__apply_f7b017a4f6bf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Global_traceForm__apply_f7b017a4f6bf



set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKG PositivityTheory.ThKG.Loc PositivityTheory.ThKG.Loc.Bump
open MeasureTheory Filter Topology Set
open scoped ComplexConjugate
variable {ι : Type} [Fintype ι]
namespace PositivityTheory.ThKG.Loc.Bump
theorem _root_.solution (κ : ι → ℕ) (x : ι → ℂ) :
    FT (gm κ) x = ∏ w, (2⁻¹ * (-Complex.I) ^ κ w) * (x w ^ κ w * Complex.exp (-2 * Real.pi * (‖x w‖ : ℂ) ^ 2)) := by
  have h1 : FT (gm κ) x = ∏ w, ∫ z : ℂ, ch (-(2 * (z * x w).re)) * (conj z ^ κ w * Complex.exp (-2 * Real.pi * (‖z‖ : ℂ) ^ 2)) := by
    rw [← integral_fintype_prod_volume_eq_prod, FT]
    congr 1; funext t
    rw [pr, ← Finset.sum_neg_distrib, ch_sum, gm, ← Finset.prod_mul_distrib]
  rw [h1]
  refine Finset.prod_congr rfl fun w _ => ?_
  have h := congrFun (GroundTheory.Global.complexFourier_conj_pow_mul_gaussian (κ w)) (x w)
  rw [GroundTheory.Global.complexFourier, GroundTheory.Global.complexPlaceMeasure, integral_smul_measure] at h
  rw [mul_assoc, ← h]
  simp only [Circle.smul_def, smul_eq_mul, Real.fourierChar_apply, ENNReal.toReal_ofNat, Complex.real_smul, Complex.ofReal_ofNat]
  rw [← mul_assoc, inv_mul_cancel₀ two_ne_zero, one_mul]
  congr 1; funext z; congr 1
  rw [ch]; congr 1; push_cast; ring
end PositivityTheory.ThKG.Loc.Bump
