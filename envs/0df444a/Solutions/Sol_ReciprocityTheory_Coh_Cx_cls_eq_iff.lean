-- Prove2me | solution 1 for ReciprocityTheory.Coh.Cx.cls_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:15:27.731076+00:00
-- url     : https://prove2.me/submissions/3f3b35b2-ac86-48a2-ba91-b0067ed500be

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
theorem _root_.solution {n : ℕ} {x y : A.X n} (hx : A.d n x = 0) (hy : A.d n y = 0) :
    A.cls n x hx = A.cls n y hy ↔ x - y ∈ A.B n := by
  unfold cls
  rw [Submodule.Quotient.eq]
  exact Iff.rfl
end ReciprocityTheory.Coh.Cx
