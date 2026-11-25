-- Prove2me | solution 1 for P2M_GlobalTheory_ZetaLocal_norm_zeta__le_8dd564b5075f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:34:16.438991+00:00
-- url     : https://prove2.me/submissions/414ccc2e-60d4-447f-bfbe-db54f4f07546

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TsumOneDivRpowLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NormOneSubConjMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DifferentiableAtFractInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LogDerivRiemannZetaLocalZeroSum
import Theorems.Thm_P2M_GlobalTheory_ZetaLocal_zeta__eq_fc7653a25de8
import Theorems.Thm_GlobalTheory_ZetaHalfPlane_norm_zeta_sub_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory GlobalTheory.ZetaLocal
namespace GlobalTheory.ZetaLocal
theorem _root_.solution (t : ℝ) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖riemannZeta₁ (3/2 + t * I + z)‖ ≤ 5 * (|t| + 2) ^ 2 := by
  have ht := abs_nonneg t
  set w : ℂ := 3/2 + t * I + z with hw
  by_cases h : w = 1
  · rw [h, riemannZeta₁_one, norm_one]; nlinarith
  have hre : 1 / 2 ≤ w.re := by
    have := (abs_le.1 ((abs_re_le_norm z).trans hz)).1
    simp [hw]; linarith
  have htI : ‖(t : ℂ) * I‖ = |t| := by simp
  have h1 : ‖w - 1‖ ≤ |t| + 2 := by
    have : w - 1 = 1/2 + t * I + z := by rw [hw]; ring
    rw [this]
    refine norm_add₃_le.trans ?_
    rw [htI]; norm_num; linarith
  have h2 : ‖w‖ ≤ 2 * (|t| + 2) := by
    refine norm_add₃_le.trans ?_
    rw [htI]; norm_num; linarith
  have h3 := GlobalTheory.ZetaHalfPlane.norm_zeta_sub_le w (by linarith) h
  have h4 : ‖w‖ / w.re ≤ 2 * ‖w‖ := by
    rw [div_le_iff₀ (by linarith)]; nlinarith [norm_nonneg w]
  have e : riemannZeta₁ w = (w - 1) * (riemannZeta w - w / (w - 1)) + w := by
    have := sub_ne_zero.2 h
    rw [zeta₁_eq h]; field_simp; ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul]
  have h5 : ‖w - 1‖ * ‖riemannZeta w - w / (w - 1)‖ ≤ (|t| + 2) * (4 * (|t| + 2)) :=
    mul_le_mul h1 (by linarith) (norm_nonneg _) (by linarith)
  nlinarith
end GlobalTheory.ZetaLocal
