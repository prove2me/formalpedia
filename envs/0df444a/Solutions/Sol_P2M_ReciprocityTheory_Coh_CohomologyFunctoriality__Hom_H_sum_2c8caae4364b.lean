-- Prove2me | solution 1 for P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__Hom_H_sum_2c8caae4364b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:58:03.918357+00:00
-- url     : https://prove2.me/submissions/f67bda7f-c224-459f-837e-a9b7debd0586

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
theorem _root_.solution {ι : Type*} (s : Finset ι) (φ : Hom A B) (ψ : ι → Hom A B) (n : ℕ)
    (h : ∀ x, φ.f n x = ∑ c ∈ s, (ψ c).f n x) (y : A.H n) :
    φ.H n y = ∑ c ∈ s, (ψ c).H n y := by
  refine Submodule.Quotient.induction_on _ y fun z => ?_
  show Submodule.Quotient.mk (φ.Z n z) = ∑ c ∈ s, Submodule.Quotient.mk ((ψ c).Z n z)
  rw [← Submodule.mkQ_apply, show (∑ c ∈ s, Submodule.Quotient.mk ((ψ c).Z n z) : B.H n) =
    ∑ c ∈ s, (Submodule.mkQ _) ((ψ c).Z n z) from rfl, ← map_sum]
  congr 1
  apply Subtype.ext
  rw [Submodule.coe_sum]
  exact h z.1
end Hom
end ReciprocityTheory.Coh.CohomologyFunctoriality₂
