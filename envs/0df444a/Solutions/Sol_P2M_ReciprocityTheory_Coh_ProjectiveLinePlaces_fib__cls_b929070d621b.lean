-- Prove2me | solution 1 for P2M_ReciprocityTheory_Coh_ProjectiveLinePlaces_fib__cls_b929070d621b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:13:36.505805+00:00
-- url     : https://prove2.me/submissions/d4cf2d84-6176-40af-bb5e-bac34bb0390d

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
theorem _root_.solution (φ : Hom A B) (n : ℕ) (b : B.X n) (hb) (h) :
    fibδ φ n (B.cls n b hb) = (fib φ).cls (n + 1) (0, b) h := rfl
end ReciprocityTheory.Coh.ProjectiveLinePlaces
