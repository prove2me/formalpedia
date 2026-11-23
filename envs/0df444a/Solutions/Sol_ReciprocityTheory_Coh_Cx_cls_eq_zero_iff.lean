-- Prove2me | solution 1 for ReciprocityTheory.Coh.Cx.cls_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:13:16.780839+00:00
-- url     : https://prove2.me/submissions/96a6a151-62b4-4e1e-aa64-83049f72a7e8

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
theorem _root_.solution {n : ℕ} {x : A.X n} (hx : A.d n x = 0) :
    A.cls n x hx = 0 ↔ x ∈ A.B n := by
  unfold cls
  rw [Submodule.Quotient.mk_eq_zero]
  exact Iff.rfl
end ReciprocityTheory.Coh.Cx
