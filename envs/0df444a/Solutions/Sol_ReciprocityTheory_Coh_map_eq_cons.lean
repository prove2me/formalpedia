-- Prove2me | solution 1 for ReciprocityTheory.Coh.map_eq_cons
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:48:20.092864+00:00
-- url     : https://prove2.me/submissions/351cbc26-9456-41e2-9fcf-aa79589e680e

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_HomogExistsStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_PrismOpZeroEval
import Theorems.Thm_ReciprocityTheory_Coh_cons_map

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
theorem _root_.solution (b : X → Y) {n : ℕ} (x : Fin (n + 1) → X) :
    (fun j => b (x j)) = Fin.cons (b (x 0)) fun j => b (Fin.tail x j) := by
  conv_lhs => rw [← Fin.cons_self_tail x]
  exact cons_map b _ _
end ReciprocityTheory.Coh
