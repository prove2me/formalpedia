-- Prove2me | solution 1 for ReciprocityTheory.Coh.prismOp_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:31:37.214746+00:00
-- url     : https://prove2.me/submissions/3281a2e6-567c-4c51-97cf-9e10974f4edd

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_HomogExistsStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_PrismOpZeroEval

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh
open Function
universe u
variable {V X Y : Type u} [AddCommGroup V]
namespace ReciprocityTheory.Coh
theorem _root_.solution (a b : X → Y) (n : ℕ) (F : (Fin (n + 3) → Y) → V) (x : Fin (n + 2) → X) :
    prismOp a b (n + 1) F x = F (Fin.cons (a (x 0)) fun j => b (x j)) -
      prismOp a b n (fun y => F (Fin.cons (a (x 0)) y)) (Fin.tail x) := rfl
end ReciprocityTheory.Coh
