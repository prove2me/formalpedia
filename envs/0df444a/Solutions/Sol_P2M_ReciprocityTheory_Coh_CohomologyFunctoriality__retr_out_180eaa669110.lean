-- Prove2me | solution 1 for P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__retr_out_180eaa669110
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:59:40.039971+00:00
-- url     : https://prove2.me/submissions/aea1d1d1-acec-4bc2-899a-64da556551dc

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_HomogExistsStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_PartialProdCoe
import Theorems.Thm_P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__rep_out_4a7c7e650af4

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
theorem _root_.solution (c : Quotient (QuotientGroup.rightRel U)) : retr U c.out = 1 := by
  apply Subtype.ext
  simp only [retr, rep_out, mul_inv_cancel, OneMemClass.coe_one]
end ReciprocityTheory.Coh.CohomologyFunctoriality₂
