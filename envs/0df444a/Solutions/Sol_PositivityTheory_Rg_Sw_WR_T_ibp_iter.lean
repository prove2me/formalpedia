-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.T.ibp_iter
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:48:14.406465+00:00
-- url     : https://prove2.me/submissions/002476b7-6444-4c41-a9dc-481f055d7072

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_DifferentiableOfTop
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_T_good_iter

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix Filter Topology
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.T
open PositivityTheory.Rg.Sw
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.T
theorem _root_.solution (hIBP : IBP) {f : E n → ℂ} (hf : Good f) (t : ℝ) (β : E n) (ht : t ≠ 0) (hβ : (herm β).det ≠ 0)
    (N : ℕ) : ∫ y, f y * chr t β y =
      ((-1) ^ n * ((-(Complex.I * t)) ^ n * (herm β).det)⁻¹) ^ N * ∫ y, (Delta^[N] f) y * chr t β y := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [ih, hIBP n (Delta^[N] f) t β (good_iter hf N).1 ht hβ (good_iter hf N).2, Function.iterate_succ_apply', pow_succ]
    ring
end PositivityTheory.Rg.Sw.WR.T
