-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_contDiffOn_hv_c131b75442aa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:30:52.26031+00:00
-- url     : https://prove2.me/submissions/5fef3f06-06e8-40d6-bfff-952c5f631ecc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_XiPluckerCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PXiMetric
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_contDiffOn_formRe_7dc4e84b9f80

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
variable {G : YPt ι ν κ → Matrix κ κ ℂ} (hG : IsEEMetric G)
include hG
namespace GroundTheory.Heights₂.Heights.Inter.XiMetricSmoothness
theorem _root_.solution : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (hv G) (goodY ι ν κ) :=
  contDiffOn_formRe (fun m n => hG.2.2.2 m n) (fun _ => (contDiff_apply ℝ ℂ _).contDiffOn)
    (fun _ => (contDiff_apply ℝ ℂ _).contDiffOn)
end GroundTheory.Heights₂.Heights.Inter.XiMetricSmoothness
