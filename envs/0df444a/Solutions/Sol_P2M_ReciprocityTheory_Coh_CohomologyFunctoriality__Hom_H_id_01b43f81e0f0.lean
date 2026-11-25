-- Prove2me | solution 1 for P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__Hom_H_id_01b43f81e0f0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:52:46.895794+00:00
-- url     : https://prove2.me/submissions/d3a41ce9-ca6a-4ac4-a4e8-3371c2247ddf

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
variable {R : Type u} [CommRing R] {A B C : Cx R}
namespace ReciprocityTheory.Coh.CohomologyFunctoriality₂
namespace Hom
theorem _root_.solution (n : ℕ) (y : A.H n) : (Hom.id A).H n y = y := by
  refine Submodule.Quotient.induction_on _ y fun z => ?_
  rfl
end Hom
end ReciprocityTheory.Coh.CohomologyFunctoriality₂
