-- Prove2me | solution 1 for ReciprocityTheory.Coh.prismOp_one_eval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:49:02.794586+00:00
-- url     : https://prove2.me/submissions/030aa24b-87b2-4635-8040-7f7f10821e60

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_HomogExistsStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_PrismOpZeroEval
import Theorems.Thm_ReciprocityTheory_Coh_prismOp_zero
import Theorems.Thm_ReciprocityTheory_Coh_prismOp_succ

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
theorem _root_.solution (a b : X → Y) (K : (Fin 3 → Y) → V) (x : Fin 2 → X) :
    prismOp a b 1 K x = K ![a (x 0), b (x 0), b (x 1)] - K ![a (x 0), a (x 1), b (x 1)] := by
  rw [prismOp_succ, prismOp_zero]
  congr 2 <;> funext j <;> fin_cases j <;> rfl
end ReciprocityTheory.Coh
