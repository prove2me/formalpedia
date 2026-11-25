-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.B.dirC_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:50:17.047348+00:00
-- url     : https://prove2.me/submissions/b5accc6f-a7ea-48d7-abd7-e35bd36be07f

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBound
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_dirC_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.B
open PositivityTheory.Rg.Sw
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.B
theorem _root_.solution {f : E n → ℂ} {y : E n} (hf : DifferentiableAt ℝ f y) (p : ℕ) (w : Fin n → Fin n → ℂ) (c : ℂ)
    (hc : dirC f w y = c * f y) : dirC (fun y => f y ^ p) w y = p * c * f y ^ p := by
  rw [dirC_comp (hasDerivAt_pow p (f y)) hf, hc]
  cases p with
  | zero => simp
  | succ p => simp only [Nat.cast_succ, Nat.add_sub_cancel, pow_succ]; ring
end PositivityTheory.Rg.Sw.WR.B
