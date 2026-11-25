-- Prove2me | solution 1 for ReciprocityTheory.Coh.prismOp_hd_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:55:16.798681+00:00
-- url     : https://prove2.me/submissions/9034119f-0972-4eca-957d-8deccd3ecee9

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_HomogExistsStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_PrismOpZeroEval
import Theorems.Thm_P2M_ReciprocityTheory_Coh_hd_zero__2cdee07dd440
import Theorems.Thm_ReciprocityTheory_Coh_prismOp_zero

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
theorem _root_.solution (a b : X → Y) (F : (Fin 1 → Y) → V) (x : Fin 1 → X) :
    prismOp a b 0 (hd 0 F) x = F (fun i => b (x i)) - F (fun i => a (x i)) := by
  rw [prismOp_zero, hd_zero', Fin.tail_cons, Fin.cons_zero]
  congr 2; funext i; rw [Subsingleton.elim i 0]
end ReciprocityTheory.Coh
