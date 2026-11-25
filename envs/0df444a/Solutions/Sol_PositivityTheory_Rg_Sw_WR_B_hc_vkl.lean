-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.B.hc_vkl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:02:16.973715+00:00
-- url     : https://prove2.me/submissions/2eea3142-37e0-4433-9774-3c0e0814fb3b

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundB
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_hc_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.B
open PositivityTheory.Rg.Sw
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.B
theorem _root_.solution (k l : Fin n) :
    herm (fun a b => (vkl k l a b).re) + Complex.I • herm (fun a b => (vkl k l a b).im) = Matrix.single l k 1 := by
  rw [hc_eq]
  have c1 : (1 + Complex.I) / 2 * ((1 + Complex.I) / 2) + (1 - Complex.I) / 2 * ((1 - Complex.I) / 2) = 0 := by
    apply Complex.ext <;> simp <;> norm_num
  have c2 : (1 + Complex.I) / 2 * ((1 - Complex.I) / 2) + (1 - Complex.I) / 2 * ((1 + Complex.I) / 2) = 1 := by
    apply Complex.ext <;> simp <;> norm_num
  ext i j
  have e1 : (j = k ∧ i = l) ↔ (i = l ∧ j = k) := and_comm
  have e2 : (j = l ∧ i = k) ↔ (i = k ∧ j = l) := and_comm
  have e3 : (l = i ∧ k = j) ↔ (i = l ∧ j = k) := ⟨fun h => ⟨h.1.symm, h.2.symm⟩, fun h => ⟨h.1.symm, h.2.symm⟩⟩
  simp only [vkl, Matrix.single_apply, e1, e2, e3]
  by_cases hA : i = k ∧ j = l <;> by_cases hB : i = l ∧ j = k
  · rw [if_pos hA, if_pos hA, if_pos hB, if_pos hB, if_pos hB]; linear_combination c1 + c2
  · rw [if_pos hA, if_pos hA, if_neg hB, if_neg hB, if_neg hB]; linear_combination c1
  · rw [if_neg hA, if_neg hA, if_pos hB, if_pos hB, if_pos hB]; linear_combination c2
  · rw [if_neg hA, if_neg hA, if_neg hB, if_neg hB, if_neg hB]; ring
end PositivityTheory.Rg.Sw.WR.B
