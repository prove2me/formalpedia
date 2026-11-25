-- Prove2me | solution 1 for P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__retr_conj_4a4d3489c1a5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:59:35.400148+00:00
-- url     : https://prove2.me/submissions/94f21e7d-4f4f-4cc8-b31a-a2ff0aeaca53

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_HomogExistsStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_PartialProdCoe
import Theorems.Thm_P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__retr_spec_78256959e114

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
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
namespace ReciprocityTheory.Coh.CohomologyFunctoriality₂
theorem _root_.solution (N : Subgroup G) [N.Normal] (s h : G) (hh : h ∈ N) :
    (retr N (s * h) : G) = s * h * (rep N s)⁻¹ := by
  rw [retr_spec]
  unfold rep
  rw [show Quotient.mk (QuotientGroup.rightRel N) (s * h) = Quotient.mk _ s from (mkR_eq N).2 (by
    have h1 := (inferInstance : N.Normal).conj_mem _ (N.inv_mem hh) s
    simpa [mul_inv_rev, mul_assoc] using h1)]
end ReciprocityTheory.Coh.CohomologyFunctoriality₂
