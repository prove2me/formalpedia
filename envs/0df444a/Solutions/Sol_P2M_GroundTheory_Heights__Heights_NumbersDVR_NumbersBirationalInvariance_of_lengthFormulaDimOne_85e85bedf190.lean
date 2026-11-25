-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_NumbersBirationalInvariance_of_lengthFormulaDimOne_85e85bedf190
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:56:11.358567+00:00
-- url     : https://prove2.me/submissions/be0ce928-db1f-48e1-8696-848ead0c7a90

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Length
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_MemOfMemSupportDivCycle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_OrdModEqLengthQuotSup
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_lengthTerm_eq_13258b0bf097
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_range_lsmul_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open Module IsLocalRing ReciprocityTheory.ChartRestriction.G.AI
universe u v
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace NumbersBirationalInvariance
theorem _root_.solution (h : LengthFormulaDimOne.Statement.{u, v}) :
    IndefiniteRowSideFullHecke.NumbersDVR.NumbersBirationalInvariance.Statement.{u, v} := by
  intro A _ _ _ M _ _ _ x hdim hfin
  have hq : (Ideal.span {x} • ⊤ : Submodule A M) = LinearMap.range (LinearMap.lsmul A M x) := by
    rw [Submodule.ideal_span_singleton_smul, range_lsmul_eq]
  have ht : Submodule.torsionBy A M x = LinearMap.ker (LinearMap.lsmul A M x) := rfl
  rw [hq] at hfin ⊢
  rw [ht, (h A M x hdim hfin).2]
  congr 1
  exact finsum_congr (lengthTerm_eq hdim M x)
end NumbersBirationalInvariance
end GroundTheory.Heights₂.Heights.NumbersDVR
