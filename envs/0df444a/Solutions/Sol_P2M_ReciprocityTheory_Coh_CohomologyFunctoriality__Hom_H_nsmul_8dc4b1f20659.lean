-- Prove2me | solution 1 for P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__Hom_H_nsmul_8dc4b1f20659
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:52:50.995481+00:00
-- url     : https://prove2.me/submissions/7ab89be3-806d-417f-b86c-70c47377ff6a

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
theorem _root_.solution (φ : Hom A A) (k : ℕ) (n : ℕ) (h : ∀ x, φ.f n x = k • x) (y : A.H n) :
    φ.H n y = k • y := by
  refine Submodule.Quotient.induction_on _ y fun z => ?_
  show Submodule.Quotient.mk (φ.Z n z) = k • Submodule.Quotient.mk z
  rw [← Submodule.Quotient.mk_smul]
  congr 1
  exact Subtype.ext (h z)
end Hom
end ReciprocityTheory.Coh.CohomologyFunctoriality₂
