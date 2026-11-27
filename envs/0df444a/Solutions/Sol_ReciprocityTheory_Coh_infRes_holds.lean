-- Prove2me | solution 1 for ReciprocityTheory.Coh.infRes_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:33:12.782725+00:00
-- url     : https://prove2.me/submissions/610a82eb-e4e3-474d-bd12-589fc0833dfb

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_LowHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_InnerHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_InfRes
import Theorems.Thm_ReciprocityTheory_Coh_InflationRestrictionInvariants_inf_inj
import Theorems.Thm_ReciprocityTheory_Coh_InflationRestrictionInvariants_inf_res_exact
import Theorems.Thm_ReciprocityTheory_Coh_InflationRestrictionInvariants_conj_res

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
theorem _root_.solution : InfResStatement.{u} := fun R _ G _ _ _ M N _ Q P hP =>
  ⟨inf_inj M N Q P hP, inf_res_exact M N Q P hP, fun s c h1 h2 n x => conj_res M N s c h1 h2 n x⟩
end ReciprocityTheory.Coh
