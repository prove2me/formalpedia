-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.B.norm_eval_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:51:06.049981+00:00
-- url     : https://prove2.me/submissions/ec9c1ab7-3c82-494c-91f3-1e153d3e5f87

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBound

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
theorem _root_.solution {σ : Type} (x : σ → ℂ) (hx : ∀ i, ‖x i‖ ≤ 1) (R : MvPolynomial σ ℂ) :
    ‖MvPolynomial.eval x R‖ ≤ ∑ m ∈ R.support, ‖MvPolynomial.coeff m R‖ := by
  rw [MvPolynomial.eval_eq]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => ?_)
  rw [norm_mul]
  have : ‖∏ i ∈ m.support, x i ^ m i‖ ≤ 1 := by
    rw [norm_prod]
    exact Finset.prod_le_one (fun _ _ => norm_nonneg _) fun i _ => by
      rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (hx i)
  calc ‖MvPolynomial.coeff m R‖ * ‖∏ i ∈ m.support, x i ^ m i‖ ≤ ‖MvPolynomial.coeff m R‖ * 1 :=
        mul_le_mul_of_nonneg_left this (norm_nonneg _)
    _ = _ := mul_one _
end PositivityTheory.Rg.Sw.WR.B
