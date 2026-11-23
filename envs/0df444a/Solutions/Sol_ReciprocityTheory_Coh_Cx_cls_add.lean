-- Prove2me | solution 1 for ReciprocityTheory.Coh.Cx.cls_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:13:18.161253+00:00
-- url     : https://prove2.me/submissions/e23c806e-4547-4f2b-b63b-dc6ce49aa4cf

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
theorem _root_.solution {n : ℕ} (x y : A.X n) (hx : A.d n x = 0) (hy : A.d n y = 0) :
    A.cls n x hx + A.cls n y hy = A.cls n (x + y) (d_add_eq_zero hx hy) := rfl
end ReciprocityTheory.Coh.Cx
