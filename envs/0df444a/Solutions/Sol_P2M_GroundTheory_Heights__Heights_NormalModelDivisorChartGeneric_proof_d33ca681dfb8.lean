-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NormalModelDivisorChartGeneric_proof_d33ca681dfb8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:04:59.592494+00:00
-- url     : https://prove2.me/submissions/df049ae8-0f79-4672-8020-43931f475a19

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModelGoodPointGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModelGoodPointChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalModelDivisorChartGeneric

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
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace NormalModelDivisorChartGeneric
theorem _root_.solution (h₁ : NormalModelGoodPointGeneric.Statement)
    (h₂ : NormalModelGoodPointChart.Statement) : NormalModelDivisorChartGeneric.Statement := by
  intro n d J u M hJ hd hu
  obtain ⟨B, hB, hBd, hgood⟩ := h₁ n d J u M hJ hd hu
  exact ⟨B, hB, hBd, fun w hw hu0 hwB => h₂ n d J u M w (hgood w hw hu0 hwB)⟩
end NormalModelDivisorChartGeneric
end GroundTheory.Heights₂.Heights
