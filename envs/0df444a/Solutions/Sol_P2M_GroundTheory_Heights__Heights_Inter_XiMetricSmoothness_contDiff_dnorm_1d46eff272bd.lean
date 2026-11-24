-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_contDiff_dnorm_1d46eff272bd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:42:58.370074+00:00
-- url     : https://prove2.me/submissions/b5dd322d-ebd1-4d73-baff-5fc11cb6dad3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_XiPluckerCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PXiMetric
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_contDiff_normSq_coord_b2ec97168040

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
theorem _root_.solution : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (dnorm : YPt ι ν κ → ℝ) :=
  ContDiff.sum fun l _ => contDiff_normSq_coord ⟨.det, l⟩
end GroundTheory.Heights₂.Heights.Inter.XiMetricSmoothness
