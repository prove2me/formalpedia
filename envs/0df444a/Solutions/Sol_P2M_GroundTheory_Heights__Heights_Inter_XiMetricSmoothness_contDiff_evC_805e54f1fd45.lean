-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_contDiff_evC_805e54f1fd45
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:34:43.51497+00:00
-- url     : https://prove2.me/submissions/255623cb-84fa-4975-91c5-ec664f08a7e6

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
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter.XiMetricSmoothness
theorem _root_.solution (f : MRing ι) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (evC f) := by
  unfold evC
  induction f using MvPolynomial.induction_on with
  | C a => simpa using contDiff_const
  | add p q hp hq => simpa using hp.add hq
  | mul_X p v hp => simpa using hp.mul (contDiff_apply ℝ ℂ v)
end GroundTheory.Heights₂.Heights.Inter.XiMetricSmoothness
