-- Prove2me | solution 1 for ReciprocityTheory.Coh.smulHom_f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:01:38.645828+00:00
-- url     : https://prove2.me/submissions/34fba825-3e8a-4224-a941-8bd501460420

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_ConnNatHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_IsSuccSubset
import Definitions.Def_ReciprocityTheory_GroupCohomology_FinGen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh
open Cx Function
universe u
variable {R : Type u} [CommRing R] (t : R) {A : ℕ → Cx R} {τ : ∀ m, Hom (A (m + 1)) (A m)}
  {L : Cx R} {π : ∀ m, Hom L (A m)}
namespace ReciprocityTheory.Coh
theorem _root_.solution (L : Cx R) (t : R) (n : ℕ) (x : L.X n) : (smulHom L t).f n x = t • x := rfl
end ReciprocityTheory.Coh
