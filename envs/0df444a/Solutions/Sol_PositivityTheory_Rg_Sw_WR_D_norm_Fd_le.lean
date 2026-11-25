-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.D.norm_Fd_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:18:33.662561+00:00
-- url     : https://prove2.me/submissions/c26cabcb-287a-4ff8-8964-03c696c9ca60

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_DensDefs
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_DerivFA
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_norm_exp_I_mul
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_norm_Lc_le
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_abs_qX_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.D
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR
variable {m n : ℕ}
variable (ε : Fin m → Bool) (c t : ℝ)
variable {ε c t}
namespace PositivityTheory.Rg.Sw.WR.D
theorem _root_.solution (P : PX m n) (y : E n) (x : Fin m → Fin n → ℂ) : ‖Fd ε c t P y x‖ ≤ bnd ε c t P x := by
  have e0 : ‖Fd ε c t P y x‖ = ‖evX P x * gs c x‖ * |t| * ‖Lc (qX ε x)‖ := by
    simp only [Fd, norm_smul, norm_mul, norm_exp_I_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
      one_mul, mul_one]
  rw [e0]
  unfold bnd
  calc ‖evX P x * gs c x‖ * |t| * ‖Lc (qX ε x)‖
      ≤ ‖evX P x * gs c x‖ * |t| * ∑ a, ∑ b, |qX ε x a b| :=
        mul_le_mul_of_nonneg_left (norm_Lc_le _) (by positivity)
    _ = |t| * ∑ a, ∑ b, ‖evX P x * gs c x‖ * |qX ε x a b| := by
        simp only [Finset.mul_sum]; refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_; ring
    _ ≤ |t| * ∑ a, ∑ b, 2 * ‖evX (Qp ε a b * P) x * gs c x‖ := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_) (abs_nonneg _)
        have h := abs_qX_le ε x a b
        have e : evX (Qp ε a b * P) x * gs c x = evX (Qp ε a b) x * (evX P x * gs c x) := by
          simp only [evX, map_mul]; ring
        rw [e]
        simp only [norm_mul]
        have hn : 0 ≤ ‖evX P x‖ * ‖gs c x‖ := by positivity
        nlinarith [mul_le_mul_of_nonneg_left h hn]
end PositivityTheory.Rg.Sw.WR.D
