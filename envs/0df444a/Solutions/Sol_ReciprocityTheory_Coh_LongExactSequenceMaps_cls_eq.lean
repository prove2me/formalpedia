-- Prove2me | solution 1 for ReciprocityTheory.Coh.LongExactSequenceMaps.cls_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:54:19.612849+00:00
-- url     : https://prove2.me/submissions/46c4f859-7949-4cd8-83b6-f9b135ff3e12

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
theorem _root_.solution (A : Cx R) (n : ℕ) (x y : A.X n) (hx : A.d n x = 0) (hy : A.d n y = 0) :
    A.cls n x hx = A.cls n y hy ↔ x - y ∈ A.B n := by
  unfold Cx.cls
  rw [Submodule.Quotient.eq]
  exact Iff.rfl
end ReciprocityTheory.Coh.LongExactSequenceMaps
