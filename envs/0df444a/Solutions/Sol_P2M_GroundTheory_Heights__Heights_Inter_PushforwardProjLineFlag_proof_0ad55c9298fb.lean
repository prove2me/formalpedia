-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_PushforwardProjLineFlag_proof_0ad55c9298fb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:01:11.388584+00:00
-- url     : https://prove2.me/submissions/ef1c89f2-654f-460f-8331-dfba20500a2e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsPFStep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PfAtZero
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_pfAt_zero_17a3e9c4fe76

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
namespace GroundTheory.Heights₂.Heights.Inter
namespace PushforwardProjLineFlag
theorem _root_.solution (hAI3 : PushforwardArithIntersection.Statement) (hStep : PFStep.Statement) : PushforwardProjLineFlag.Statement := by
  intro I hI K _ ι _ K' _ ι' _ κ v P' d r
  have key : ∀ r, PFAt I r := fun r =>
    Nat.rec (pfAt_zero hAI3 I hI) (fun r h => hStep I hI r h) r
  exact key r K ι K' ι' κ v P' d
end PushforwardProjLineFlag
end GroundTheory.Heights₂.Heights.Inter
