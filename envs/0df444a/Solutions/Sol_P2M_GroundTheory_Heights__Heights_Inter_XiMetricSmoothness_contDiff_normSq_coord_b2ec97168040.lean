-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_contDiff_normSq_coord_b2ec97168040
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:30:52.895802+00:00
-- url     : https://prove2.me/submissions/3f568474-0b73-49c8-8f35-03449af65d94

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_XiPluckerCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PXiMetric

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial Matrix ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
open scoped ComplexOrder
set_option linter.unusedSectionVars false
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.XiMetricSmoothness
variable {ι ν κ : Type} [Fintype ι] [Fintype ν] [Fintype κ]
namespace GroundTheory.Heights₂.Heights.Inter.XiMetricSmoothness
theorem _root_.solution (p : Σ k, T.yyIdx ι ν κ k) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w : YPt ι ν κ => ‖w p‖ ^ 2) :=
  (contDiff_norm_sq ℝ).comp (contDiff_apply ℝ ℂ p)
end GroundTheory.Heights₂.Heights.Inter.XiMetricSmoothness
