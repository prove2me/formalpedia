-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartHessianComparison_cxHessian_affine_c3056775183d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:48:16.524781+00:00
-- url     : https://prove2.me/submissions/a8463385-8ced-4562-a74c-3ae9122b4e6b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartHessCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsHermFormCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartDensityIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ChartGramHess
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartHessCompare
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartGram_cxHessian_half_log_379ffacce966


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
open ReciprocityTheory.ChartRestriction.G.Geo Matrix
open scoped ComplexOrder InnerProductSpace
noncomputable section
open GroundTheory.Heights₂.Heights.ChartHessianComparison
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {e : ℕ}
namespace GroundTheory.Heights₂.Heights.ChartHessianComparison
theorem _root_.solution [CompleteSpace F] (c : F) (L : (Fin e → ℂ) →L[ℂ] F) (y : Fin e → ℂ)
    (h0 : c + L y ≠ 0) :
    cxHessian (fun y' => 2⁻¹ * Real.log (⟪c + L y', c + L y'⟫_ℂ).re) y =
      gramHess (c + L y) (fun j => L (Pi.single j 1)) := by
  have hu : ∀ᶠ y' in nhds y, AnalyticAt ℂ (fun y' => c + L y') y' :=
    Filter.Eventually.of_forall fun y' => analyticAt_const.add (L.analyticAt y')
  have hd : fderiv ℂ (fun y' => c + L y') y = L := by
    rw [fderiv_const_add]; exact L.fderiv
  ext i j
  rw [ChartGram.cxHessian_half_log hu h0 i j, hd]
  rfl
end GroundTheory.Heights₂.Heights.ChartHessianComparison
