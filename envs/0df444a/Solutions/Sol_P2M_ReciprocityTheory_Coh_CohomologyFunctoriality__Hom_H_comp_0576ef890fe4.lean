-- Prove2me | solution 1 for P2M_ReciprocityTheory_Coh_CohomologyFunctoriality__Hom_H_comp_0576ef890fe4
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:15:30.584147+00:00
-- url     : https://prove2.me/submissions/eded99d3-19c7-4acd-8e1e-48eea3bec533

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
theorem _root_.solution (φ : Hom A B) (ψ : Hom B C) (n : ℕ) (y : A.H n) :
    (ψ.comp φ).H n y = ψ.H n (φ.H n y) := by
  refine Submodule.Quotient.induction_on _ y fun z => ?_
  rfl
end Hom
end ReciprocityTheory.Coh.CohomologyFunctoriality₂
