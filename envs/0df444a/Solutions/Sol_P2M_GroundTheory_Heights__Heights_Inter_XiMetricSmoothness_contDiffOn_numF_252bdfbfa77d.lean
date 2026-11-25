-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_contDiffOn_numF_252bdfbfa77d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:30:53.176298+00:00
-- url     : https://prove2.me/submissions/a2bce647-db33-4263-ae42-dc17b047b9e2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_XiPluckerCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PXiMetric
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_contDiffOn_formRe_7dc4e84b9f80
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_contDiff_evC_805e54f1fd45

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
theorem _root_.solution (F : ι → ν → κ → κ → MRing (T.yyIdx ι ν κ)) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (numF G F) (goodY ι ν κ) := by
  unfold numF tensQ
  refine ContDiffOn.sum fun i _ => ContDiffOn.sum fun l _ => ?_
  refine contDiffOn_formRe (M := fun w => Matrix.kronecker (G w) (G w)) (fun p q => ?_)
    (fun p => (contDiff_evC _).contDiffOn) (fun p => (contDiff_evC _).contDiffOn)
  simp only [Matrix.kronecker, kroneckerMap_apply]
  exact (hG.2.2.2 p.1 q.1).mul (hG.2.2.2 p.2 q.2)
end GroundTheory.Heights₂.Heights.Inter.XiMetricSmoothness
