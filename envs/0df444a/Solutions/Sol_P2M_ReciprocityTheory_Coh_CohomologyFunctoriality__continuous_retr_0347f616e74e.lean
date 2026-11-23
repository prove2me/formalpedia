-- Prove2me | solution 1 for P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__continuous_retr_0347f616e74e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:23:15.136265+00:00
-- url     : https://prove2.me/submissions/efda3ff1-4a75-4f45-a808-746be0bdc7e4

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_HomogExistsStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_PartialProdCoe
import Theorems.Thm_P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__continuous_rep_745e730e9170

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh
open ReciprocityTheory.Coh.CohomologyFunctoriality₂
open ReciprocityTheory.Gal Cx Function
noncomputable section
universe u
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (U : Subgroup G)
namespace ReciprocityTheory.Coh.CohomologyFunctoriality₂
theorem _root_.solution (hU : IsOpen (U : Set G)) : Continuous (retr U) :=
  (continuous_id.mul ((continuous_rep U hU).inv)).subtype_mk _
end ReciprocityTheory.Coh.CohomologyFunctoriality₂
