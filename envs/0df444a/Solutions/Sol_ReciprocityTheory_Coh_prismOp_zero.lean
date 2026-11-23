-- Prove2me | solution 1 for ReciprocityTheory.Coh.prismOp_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:34:49.124919+00:00
-- url     : https://prove2.me/submissions/84dd0f8b-4ee7-44ee-bf3e-3ee93890e5f3

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
theorem _root_.solution (a b : X → Y) (F : (Fin 2 → Y) → V) (x : Fin 1 → X) :
    prismOp a b 0 F x = F (Fin.cons (a (x 0)) fun j => b (x j)) := rfl
end ReciprocityTheory.Coh
