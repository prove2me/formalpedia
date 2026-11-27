-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_XiMetric_proof_0f2470f8d881
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:02:09.814931+00:00
-- url     : https://prove2.me/submissions/0a8e3e88-eff9-40f3-a41e-dbcdeb3082e3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_XiPluckerCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PXiMetric
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_isSmoothHerm_xiLine_bf571b29d24a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_xiH_identity_cd3d2b67d6ae

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
namespace GroundTheory.Heights₂.Heights.Inter
namespace XiMetric
theorem _root_.solution (hRel : PluckerRel.Statement) (hCov : PluckerCover.Statement) : XiMetric.Statement := by
  intro D S
  obtain ⟨N, F, hF⟩ := hRel D S
  obtain ⟨q, r, b, hr, hrl, hrW, hcov⟩ := hCov D S N F hF
  exact ⟨XiMetricSmoothness.xiLine S.metric hF.1 hr hrl hcov, rfl,
    XiMetricSmoothness.isSmoothHerm_xiLine S.metric hF.1 hr hrl hcov, fun z hz => XiMetricSmoothness.xiH_identity S hF hr hrl hrW hz⟩
end XiMetric
end GroundTheory.Heights₂.Heights.Inter
