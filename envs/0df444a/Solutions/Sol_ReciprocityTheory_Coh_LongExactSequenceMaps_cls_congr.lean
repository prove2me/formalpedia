-- Prove2me | solution 1 for ReciprocityTheory.Coh.LongExactSequenceMaps.cls_congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:31:49.58591+00:00
-- url     : https://prove2.me/submissions/c8996c47-8b2a-4c78-91fe-2d1565e993ef

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
theorem _root_.solution (A : Cx R) (n : ℕ) (x y : A.X n) (hx : A.d n x = 0) (hy : A.d n y = 0)
    (h : x = y) : A.cls n x hx = A.cls n y hy := by
  subst h
  rfl
end ReciprocityTheory.Coh.LongExactSequenceMaps
