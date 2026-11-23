-- Prove2me | solution 1 for ReciprocityTheory.Coh.ProjectiveLinePlaces.H_cls
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:43:52.220587+00:00
-- url     : https://prove2.me/submissions/e9cf336f-fd65-4fba-b4cd-73d49680cecb

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
theorem _root_.solution (φ : Hom A B) (n : ℕ) (x : A.X n) (hx) :
    φ.H n (A.cls n x hx) = B.cls n (φ.f n x) (by rw [← φ.comm, hx, map_zero]) := rfl
end ReciprocityTheory.Coh.ProjectiveLinePlaces
