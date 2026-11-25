-- Prove2me | solution 1 for ReciprocityTheory.Coh.CCA.pp_trunc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:46:03.977304+00:00
-- url     : https://prove2.me/submissions/d882bbe9-1443-489f-87c2-f4d75242ec15

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupCorA
import Definitions.Def_ReciprocityTheory_GroupCohomology_CupCorB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh ReciprocityTheory.Coh.CCA
open ReciprocityTheory.Gal Cx Function
noncomputable section
universe u
namespace ReciprocityTheory.Coh.CCA
theorem _root_.solution {K : Type*} [Monoid K] {p q : ℕ} (g : Fin (p + q) → K) (k : Fin (p + 1)) :
    Fin.partialProd (fun i : Fin p => g (Fin.castAdd q i)) k = Fin.partialProd g ⟨k, by omega⟩ := by
  simp only [Fin.partialProd]
  rw [List.ofFn_add, List.take_append_of_le_length (by rw [List.length_ofFn]; exact Nat.lt_succ_iff.mp k.isLt)]
  rfl
end ReciprocityTheory.Coh.CCA
