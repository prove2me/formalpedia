-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_LelongWeightDiff_measurable_chartDens_039b8fbc9b8f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:39:57.166729+00:00
-- url     : https://prove2.me/submissions/852d019f-661b-4c46-9e69-59f90bad2add

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StLelongWeightDiff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOffDominated
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PLelongWeightDiffLemmas
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_FibreBound_proof_4038dff927b3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CutOffDominated_chartDens_congr_zeroSet_8fa8af5e5701
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CutOffDominated_proof_e9b099c76968
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetSumMeasurable_isClosed_zeroSet_b1e5ce62660e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetSumMeasurable_proof_de88497bcca1


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open GroundTheory.Heights₂.Heights.Targets.LelongWeightDiff
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.Targets.LelongWeightDiff
theorem _root_.solution {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    {f : (Fin n → ℂ) → ℝ} {ψ : Fin d → (Fin n → ℂ) → ℝ} (hJ : J.IsPrime)
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d) (hA : IsFiniteProjection J A)
    (hf : ContinuousOn f (zeroSet J)) (hψ : ∀ i, SmoothNear (zeroSet J) (ψ i)) :
    Measurable (chartDens J A f ψ) := by
  classical
  rw [CutOffDominated.chartDens_congr_zeroSet (g := (zeroSet J).piecewise f 0)
    (fun x hx => (Set.piecewise_eq_of_mem _ _ _ hx).symm)]
  exact (SheetSumMeasurable.proof n d J A _ ψ hJ hdim hA
    (hf.measurable_piecewise continuousOn_const (SheetSumMeasurable.isClosed_zeroSet J).measurableSet) hψ).1
end GroundTheory.Heights₂.Heights.Targets.LelongWeightDiff
