-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.Z.herm_vkl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:58:11.446285+00:00
-- url     : https://prove2.me/submissions/8f9547a2-4873-414a-bc96-f8ab39218fe2

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainA
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_Z_hermC_eq

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.Z
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.Z
theorem _root_.solution (k l : Fin n) :
    hermL (fun a b => (vkl k l a b).re) + Complex.I • hermL (fun a b => (vkl k l a b).im) = eU l k := by
  rw [hermC_eq]
  funext i j
  have c1 : (j = k ∧ i = l) ↔ (i = l ∧ j = k) := and_comm
  have c2 : (j = l ∧ i = k) ↔ (i = k ∧ j = l) := and_comm
  simp only [vkl, eU, c1, c2]
  split_ifs <;>
    first
    | linear_combination (1 / 2 : ℂ) * Complex.I_sq
    | linear_combination (-1 / 2 : ℂ) * Complex.I_sq
    | ring1
end PositivityTheory.Rg.Sw.WR.Z
