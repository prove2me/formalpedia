-- Prove2me | solution 1 for ReciprocityTheory.Coh.CCA.prod_castAdd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:46:10.199656+00:00
-- url     : https://prove2.me/submissions/5941a2a4-99a2-4e41-9311-889424a039ac

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
theorem _root_.solution {K : Type*} [Monoid K] {p q : ℕ} (g : Fin (p + q) → K) :
    (List.ofFn fun i : Fin p => g (Fin.castAdd q i)).prod = Fin.partialProd g ⟨p, by omega⟩ := by
  simp only [Fin.partialProd]
  rw [List.ofFn_add, List.take_append_of_le_length (by simp), List.take_of_length_le (by simp)]
  rfl
end ReciprocityTheory.Coh.CCA
