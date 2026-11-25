-- Prove2me | solution 1 for ReciprocityTheory.Coh.hd_zero_eval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:47:56.908929+00:00
-- url     : https://prove2.me/submissions/0c41add1-e3dd-469f-abcb-f254419877c6

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_HomogExistsStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_PrismOpZeroEval
import Theorems.Thm_P2M_ReciprocityTheory_Coh_hd_zero__2cdee07dd440

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
theorem _root_.solution (G : (Fin 1 → X) → V) (x : Fin 2 → X) : hd 0 G x = G ![x 1] - G ![x 0] := by
  rw [hd_zero']
  congr 2 <;> funext j <;> fin_cases j <;> rfl
end ReciprocityTheory.Coh
