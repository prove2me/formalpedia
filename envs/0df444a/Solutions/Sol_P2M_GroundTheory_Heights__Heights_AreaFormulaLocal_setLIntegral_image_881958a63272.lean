-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AreaFormulaLocal_setLIntegral_image_881958a63272
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:36:30.73969+00:00
-- url     : https://prove2.me/submissions/8dd294f6-7ca7-4f19-ae4d-0e8f855539e6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsAreaFormulaLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAreaGraph
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAreaGraphBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAreaGraphPiece
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAreaGraphPartition
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGraphJacContinuous
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetImageAreaSetFrame
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PAreaFormulaLocal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AreaFormulaLocal_normDet_comp_of_norm_ca1a2bf1be84

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Module Set
open scoped ENNReal
noncomputable section
open GroundTheory.Heights₂.Heights.AreaFormulaLocal
namespace GroundTheory.Heights₂.Heights.AreaFormulaLocal
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {k : ℕ} (hk : finrank ℝ E = k)
    {B : Set E} (hB : MeasurableSet B) {a : E → EuclideanSpace ℝ (Fin k)}
    {a' : E → E →L[ℝ] EuclideanSpace ℝ (Fin k)} (ha' : ∀ x ∈ B, HasFDerivWithinAt a (a' x) B x)
    (hinj : InjOn a B) (g : EuclideanSpace ℝ (Fin k) → ℝ≥0∞) :
    ∫⁻ y in a '' B, g y ∂(μH[(k : ℝ)]) =
      ∫⁻ x in B, g (a x) *
        ENNReal.ofReal (a' x : E →ₗ[ℝ] EuclideanSpace ℝ (Fin k)).normDet ∂(μH[(k : ℝ)]) := by
  let R : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k) := ((stdOrthonormalBasis ℝ E).reindex (finCongr hk)).repr
  let Rs : EuclideanSpace ℝ (Fin k) →L[ℝ] E := (R.symm.toContinuousLinearEquiv : _ →L[ℝ] E)
  have : (μH[(k : ℝ)] : Measure E).IsAddHaarMeasure := by
    have := isAddHaarMeasure_hausdorffMeasure (E := E)
    rwa [hk] at this
  have himg : a '' B = R '' ((fun x => R.symm (a x)) '' B) := by
    rw [image_image]
    simp
  have hpres : MeasurePreserving R (μH[(k : ℝ)]) (μH[(k : ℝ)]) :=
    R.toIsometryEquiv.measurePreserving_hausdorffMeasure (k : ℝ)
  have hemb : MeasurableEmbedding R := R.toHomeomorph.measurableEmbedding
  rw [himg, ← hpres.setLIntegral_comp_emb hemb,
    lintegral_image_eq_lintegral_abs_det_fderiv_mul (μH[(k : ℝ)]) hB
      (f := fun x => R.symm (a x)) (f' := fun x => Rs.comp (a' x))
      (fun x hx => Rs.hasFDerivAt.comp_hasFDerivWithinAt x (ha' x hx))
      (fun x hx y hy hxy => hinj hx hy (R.symm.injective hxy))]
  refine setLIntegral_congr_fun hB fun x _ => ?_
  have hN : |(Rs.comp (a' x)).det| = (a' x : E →ₗ[ℝ] EuclideanSpace ℝ (Fin k)).normDet := by
    rw [ContinuousLinearMap.det, ← LinearMap.normDet_eq_abs_det]
    exact normDet_comp_of_norm (Rs : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] E) (fun v => by simp [Rs])
      (a' x : E →ₗ[ℝ] EuclideanSpace ℝ (Fin k))
  simp only [LinearIsometryEquiv.apply_symm_apply]
  rw [hN, mul_comm]
end GroundTheory.Heights₂.Heights.AreaFormulaLocal
