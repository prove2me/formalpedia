-- Prove2me | solution 1 for P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__rep_mul_d1c6e7d42e8b
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:13:31.107998+00:00
-- url     : https://prove2.me/submissions/726c7215-b638-4ce0-b82f-08ff53efee08

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
theorem _root_.solution (x : U) (g : G) : rep U ((x : G) * g) = rep U g := by
  unfold rep
  rw [show Quotient.mk (QuotientGroup.rightRel U) ((x : G) * g) = Quotient.mk _ g from
    (mkR_eq U).2 (by simpa [mul_inv_rev, mul_assoc] using U.inv_mem x.2)]
end ReciprocityTheory.Coh.CohomologyFunctoriality₂
