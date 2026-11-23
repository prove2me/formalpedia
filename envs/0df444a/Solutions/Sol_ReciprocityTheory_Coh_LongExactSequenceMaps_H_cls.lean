-- Prove2me | solution 1 for ReciprocityTheory.Coh.LongExactSequenceMaps.H_cls
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:31:38.356209+00:00
-- url     : https://prove2.me/submissions/7256198b-0028-4120-823a-49817b2d9b1d

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_ConnNatHolds

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
open ReciprocityTheory.Coh.LongExactSequenceMaps
variable {R : Type u} [CommRing R] {A B C : Cx R}
namespace ReciprocityTheory.Coh.LongExactSequenceMaps
theorem _root_.solution (φ : Hom A B) (n : ℕ) (x : A.X n) (hx : A.d n x = 0) :
    φ.H n (A.cls n x hx) = B.cls n (φ.f n x) (by rw [← φ.comm, hx, map_zero]) := rfl
end ReciprocityTheory.Coh.LongExactSequenceMaps
