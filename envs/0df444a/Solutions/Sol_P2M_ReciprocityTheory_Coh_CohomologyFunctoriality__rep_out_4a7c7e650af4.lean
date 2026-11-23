-- Prove2me | solution 1 for P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__rep_out_4a7c7e650af4
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:16:09.311422+00:00
-- url     : https://prove2.me/submissions/89b85b12-daac-494c-a020-2b82a0d9e84c

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_HomogExistsStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_PartialProdCoe

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
theorem _root_.solution (c : Quotient (QuotientGroup.rightRel U)) : rep U c.out = c.out := by
  unfold rep
  rw [Quotient.out_eq]
end ReciprocityTheory.Coh.CohomologyFunctoriality₂
