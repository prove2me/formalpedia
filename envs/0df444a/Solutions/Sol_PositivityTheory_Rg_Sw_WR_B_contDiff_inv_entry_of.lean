-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.B.contDiff_inv_entry_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:38:04.00098+00:00
-- url     : https://prove2.me/submissions/7d1f8830-08bd-4b95-a635-f990d9a37574

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundB
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_contDiff_det_of

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
theorem _root_.solution {M : E n → Matrix (Fin n) (Fin n) ℂ}
    (h : ∀ a b, ContDiff ℝ (⊤ : ℕ∞) (fun y => M y a b)) (hd : ∀ y, (M y).det ≠ 0) (a b : Fin n) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y => (M y)⁻¹ a b) := by
  have e : (fun y => (M y)⁻¹ a b) = fun y => ((M y).det)⁻¹ * ((M y).updateRow b (Pi.single a 1)).det := by
    funext y
    rw [Matrix.inv_def, Matrix.smul_apply, Matrix.adjugate_apply, Ring.inverse_eq_inv', smul_eq_mul]
  rw [e]
  refine ((contDiff_det_of h).inv hd).mul (contDiff_det_of fun i j => ?_)
  by_cases hi : i = b
  · subst hi; simpa [Matrix.updateRow_self] using contDiff_const
  · simpa [Matrix.updateRow_ne hi] using h i j
end PositivityTheory.Rg.Sw.WR.B
