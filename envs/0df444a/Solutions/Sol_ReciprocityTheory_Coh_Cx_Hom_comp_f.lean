-- Prove2me | solution 1 for ReciprocityTheory.Coh.Cx.Hom.comp_f
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:13:17.492265+00:00
-- url     : https://prove2.me/submissions/976b277e-f05f-4dc6-a5e3-ab0126556ada

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh
universe u
open ReciprocityTheory.Coh.Cx
variable {R : Type u} [CommRing R] {A B C : Cx R}
namespace ReciprocityTheory.Coh.Cx
namespace Hom
theorem _root_.solution (ψ : Hom B C) (φ : Hom A B) (n : ℕ) (x : A.X n) :
    (ψ.comp φ).f n x = ψ.f n (φ.f n x) := rfl
end Hom
end ReciprocityTheory.Coh.Cx
