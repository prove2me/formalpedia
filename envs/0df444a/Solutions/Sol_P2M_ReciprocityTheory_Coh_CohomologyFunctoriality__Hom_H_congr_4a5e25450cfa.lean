-- Prove2me | solution 1 for P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__Hom_H_congr_4a5e25450cfa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:52:42.686349+00:00
-- url     : https://prove2.me/submissions/600a824e-1c80-4a21-b627-3602d92bfeaa

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
theorem _root_.solution (φ ψ : Hom A B) (h : ∀ n x, φ.f n x = ψ.f n x) (n : ℕ) : φ.H n = ψ.H n := by
  apply LinearMap.ext
  intro y
  refine Submodule.Quotient.induction_on _ y fun z => ?_
  show Submodule.Quotient.mk (φ.Z n z) = Submodule.Quotient.mk (ψ.Z n z)
  congr 1
  exact Subtype.ext (h n z)
end Hom
end ReciprocityTheory.Coh.CohomologyFunctoriality₂
