-- Prove2me | solution 1 for ReciprocityTheory.Coh.Cx.cls_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:13:17.042793+00:00
-- url     : https://prove2.me/submissions/4acd055a-9059-4386-a0d0-163492f3af02

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
theorem _root_.solution {n : ℕ} (r : R) (x : A.X n) (hx : A.d n x = 0) :
    r • A.cls n x hx = A.cls n (r • x) (d_smul_eq_zero r hx) := rfl
end ReciprocityTheory.Coh.Cx
