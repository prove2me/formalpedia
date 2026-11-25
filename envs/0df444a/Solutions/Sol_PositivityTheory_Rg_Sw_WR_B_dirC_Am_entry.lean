-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.B.dirC_Am_entry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:16:13.507492+00:00
-- url     : https://prove2.me/submissions/0cc9077d-df17-47db-9050-18064c606596

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundB
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_dirC_const
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_dirC_add
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_dirC_mul
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_diffAt_of
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_dirC_herm_entry
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_contDiff_herm_entry

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
theorem _root_.solution (s : ℂ) (y : E n) (a b k l : Fin n) :
    dirC (fun y => Am s y a b) (vkl k l) y = -(Complex.I * s * Matrix.single l k (1 : ℂ) a b) := by
  simp only [Am, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  have h1 := diffAt_of (contDiff_herm_entry a b) y
  rw [show (fun y => (1 : Matrix (Fin n) (Fin n) ℂ) a b - Complex.I * s * herm y a b) =
      fun y => (1 : Matrix (Fin n) (Fin n) ℂ) a b + (-(Complex.I * s)) * herm y a b by funext; ring]
  rw [dirC_add (f := fun _ => (1 : Matrix (Fin n) (Fin n) ℂ) a b) (g := fun y => (-(Complex.I * s)) * herm y a b)
    (differentiableAt_const _) ((differentiableAt_const _).mul h1), dirC_const,
    dirC_mul (f := fun _ => -(Complex.I * s)) (g := fun y => herm y a b) (differentiableAt_const _) h1, dirC_const,
    dirC_herm_entry]
  ring
end PositivityTheory.Rg.Sw.WR.B
