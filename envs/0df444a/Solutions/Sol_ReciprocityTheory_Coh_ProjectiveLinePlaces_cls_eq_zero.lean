-- Prove2me | solution 1 for ReciprocityTheory.Coh.ProjectiveLinePlaces.cls_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:54:29.017704+00:00
-- url     : https://prove2.me/submissions/d03f0a15-939b-409b-8685-003d815b2e42

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_ConnNatHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_FiberFirstH0Injective

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
noncomputable section
universe u
open ReciprocityTheory.Coh.ProjectiveLinePlaces
variable {R : Type u} [CommRing R] {A B : Cx R}
namespace ReciprocityTheory.Coh.ProjectiveLinePlaces
theorem _root_.solution (A : Cx R) (n : ℕ) (x : A.X n) (hx) : A.cls n x hx = 0 ↔ x ∈ A.B n := by
  unfold Cx.cls; rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]; rfl
end ReciprocityTheory.Coh.ProjectiveLinePlaces
