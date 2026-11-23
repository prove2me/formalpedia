-- Prove2me | solution 1 for ReciprocityTheory.Coh.Cx.Hom.H_cls
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:13:16.300139+00:00
-- url     : https://prove2.me/submissions/ffad53a7-db24-44ac-9b1c-8e2c5f7d0944

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
theorem _root_.solution (φ : Hom A B) {n : ℕ} (x : A.X n) (hx : A.d n x = 0) :
    φ.H n (A.cls n x hx) = B.cls n (φ.f n x) (φ.d_f_eq_zero hx) := rfl
end Hom
end ReciprocityTheory.Coh.Cx
