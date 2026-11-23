-- Prove2me | solution 1 for P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__card_rightRel_dc20959744a5
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:16:29.54268+00:00
-- url     : https://prove2.me/submissions/e60eee5d-7c58-4e2e-aaa4-b98743d81ac5

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
theorem _root_.solution [U.FiniteIndex] [Fintype (Quotient (QuotientGroup.rightRel U))] :
    Fintype.card (Quotient (QuotientGroup.rightRel U)) = U.index := by
  rw [Subgroup.index, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel U)
end ReciprocityTheory.Coh.CohomologyFunctoriality₂
