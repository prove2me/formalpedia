-- Prove2me | solution 1 for ReciprocityTheory.Coh.invRep_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:28:33.481675+00:00
-- url     : https://prove2.me/submissions/e8e05369-5045-470b-8c6c-ae6e96bd4f9f

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_LowHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_InnerHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_InfRes
import Theorems.Thm_ReciprocityTheory_Coh_InflationRestrictionInvariants_invariants_isInvRep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh
open InflationRestrictionInvariants
universe u
namespace ReciprocityTheory.Coh
theorem _root_.solution : InvRepStatement.{u} := fun R _ G _ _ _ M N _ =>
  ⟨invQ M N, invP M N, invariants_isInvRep M N⟩
end ReciprocityTheory.Coh
