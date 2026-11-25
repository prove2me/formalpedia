-- Prove2me | solution 1 for PositivityTheory.ThKCT.Arch.Bd.shift_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:00:04.411702+00:00
-- url     : https://prove2.me/submissions/245a7753-f08c-4471-aa7c-8b55d4dc1ec3

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_SmallCones_SliceArch
import Theorems.Thm_PositivityTheory_ThKCT_Arch_peetre

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKCT PositivityTheory.ThKCT.Arch
open scoped ContDiff NNReal
open Complex Filter Topology
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
namespace PositivityTheory.ThKCT.Arch
namespace Bd
theorem _root_.solution {m : ℕ} {f : V → ℂ} (hf : ContDiff ℝ ∞ f) {C : ℝ} (h : Bd (m + 1) f C) (t : V) :
    Bd m (fun x => f (x + t) - f x) ((1 + ‖t‖) ^ m * C * ‖t‖) := by
  intro j hj x
  have hj' : ContDiff ℝ j f := hf.of_le (by exact_mod_cast le_top)
  have e : iteratedFDeriv ℝ j (fun x => f (x + t) - f x) x = iteratedFDeriv ℝ j f (x + t) - iteratedFDeriv ℝ j f x := by
    rw [← iteratedFDeriv_comp_add_right]
    exact iteratedFDeriv_sub_apply (f := fun x => f (x + t)) (hj'.comp (contDiff_id.add contDiff_const)).contDiffAt hj'.contDiffAt
  have hd : Differentiable ℝ (iteratedFDeriv ℝ j f) := hf.differentiable_iteratedFDeriv (by exact_mod_cast ENat.coe_lt_top j)
  have hp : 0 < (1 + ‖x‖) ^ m := by positivity
  have := (convex_closedBall x ‖t‖).norm_image_sub_le_of_norm_fderiv_le (f := iteratedFDeriv ℝ j f)
    (C := (1 + ‖t‖) ^ m * C / (1 + ‖x‖) ^ m) (fun y _ => hd y) (fun y hy => by
      rw [norm_fderiv_iteratedFDeriv, le_div_iff₀ hp, mul_comm]
      refine le_trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity)
        (peetre x y (r := ‖t‖) (by simpa [dist_eq_norm] using hy)) m) (norm_nonneg _)) ?_
      rw [mul_pow, mul_assoc]
      refine mul_le_mul_of_nonneg_left (le_trans ?_ (h (j + 1) (by omega) y)) (by positivity)
      exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by linarith [norm_nonneg y]) (Nat.le_succ m)) (norm_nonneg _))
    (Metric.mem_closedBall_self (norm_nonneg t)) (y := x + t) (by simp)
  rw [e, mul_comm, ← le_div_iff₀ hp]
  refine this.trans (le_of_eq ?_)
  rw [add_sub_cancel_left]; ring
end Bd
end PositivityTheory.ThKCT.Arch
