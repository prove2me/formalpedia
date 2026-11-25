-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_CutOffBoundaryBound_integrable_chartDens_a8487f280a6d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:32:24.672073+00:00
-- url     : https://prove2.me/submissions/cbdba546-d1f5-452f-83a9-8e194a9adf07

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCutOffBoundaryBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCutOffBoundaryParts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOffGradient
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_OsgoodSeparate
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOffBoundaryBound
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CutOffBoundaryBound_measurable_chartDens_139c3ef937de
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_abs_chartDens_le_2f3f1c71cee6


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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open scoped ContDiff
noncomputable section
open GroundTheory.Heights₂.Heights.CutOffBoundaryBound
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.CutOffBoundaryBound
theorem _root_.solution (hM : ChartMassCompact.Statement) {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {A : Matrix (Fin d) (Fin n) ℂ} (hJ : J.IsPrime) (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d)
    (hA : IsFiniteProjection J A) {f : (Fin n → ℂ) → ℝ} (hf : ContinuousOn f (zeroSet J))
    {ψ : Fin d → (Fin n → ℂ) → ℝ} (hψ : ∀ i, SmoothNear (zeroSet J) (ψ i))
    (hc : HasCompactSupport f ∨ ∃ i, HasCompactSupport (ψ i)) : Integrable (chartDens J A f ψ) :=
  (hM n d J A f ψ hJ hdim hA hf hψ hc).mono' (measurable_chartDens hJ hdim hA hf hψ).aestronglyMeasurable
    (Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using abs_chartDens_le J A f ψ y)
end GroundTheory.Heights₂.Heights.CutOffBoundaryBound
