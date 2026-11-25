-- Prove2me | solution 1 for ReciprocityTheory.Coh.prismOp_zero_eval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:54:35.641804+00:00
-- url     : https://prove2.me/submissions/01b3863a-2a9b-40c6-a9ab-578320facf5c

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_HomogExistsStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_PrismOpZeroEval
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
theorem _root_.solution (a b : X → Y) (F : (Fin 2 → Y) → V) (x : Fin 1 → X) :
    prismOp a b 0 F x = F ![a (x 0), b (x 0)] := by
  rw [prismOp_zero]; congr 1; funext j; fin_cases j <;> rfl
end ReciprocityTheory.Coh
