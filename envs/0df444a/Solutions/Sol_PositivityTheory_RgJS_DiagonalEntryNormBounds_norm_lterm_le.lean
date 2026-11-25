-- Prove2me | solution 1 for PositivityTheory.RgJS.DiagonalEntryNormBounds.norm_lterm_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:54:40.602123+00:00
-- url     : https://prove2.me/submissions/77d680a7-f211-44e9-acc1-feb1591e41ce

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_NewtonLow
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_DiagonalTermNorms_ConvergenceOfLandauEuler
import Theorems.Thm_PositivityTheory_RgJS_DiagonalEntryNormBounds_norm_lterm
import Theorems.Thm_PositivityTheory_RgJS_DiagonalEntryNormBounds_norm_lterm_diag

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open PositivityTheory PositivityTheory.RgJS
open PositivityTheory.RgJS.DiagonalEntryNormBounds
variable {W : Type} (q : W → ℕ)
namespace PositivityTheory.RgJS.DiagonalEntryNormBounds
theorem _root_.solution {A B : Type} [Fintype A] [Fintype B] (hq : ∀ w, 2 ≤ q w) (α : W → A → ℂ) (β : W → B → ℂ)
    (σ : ℝ) (p : W × ℕ) :
    ‖lterm q α β σ p‖ ≤ (‖lterm q α α σ p‖ + ‖lterm q β β σ p‖) / 2 := by
  rw [norm_lterm q hq, norm_lterm_diag q hq, norm_lterm_diag q hq]
  unfold cd
  set u := ‖∑ a, α p.1 a ^ (p.2 + 1)‖
  set v := ‖∑ b, β p.1 b ^ (p.2 + 1)‖
  set e := Real.exp (-(ll q p * σ))
  have he : 0 ≤ e := (Real.exp_pos _).le
  have hk : (0 : ℝ) < (p.2 : ℝ) + 1 := by positivity
  have h2 : u * v ≤ (u ^ 2 + v ^ 2) / 2 := by nlinarith [sq_nonneg (u - v)]
  have e1 : (u ^ 2 / ((p.2 : ℝ) + 1) * e + v ^ 2 / ((p.2 : ℝ) + 1) * e) / 2 =
      ((u ^ 2 + v ^ 2) / 2 * e) / ((p.2 : ℝ) + 1) := by field_simp
  rw [e1]
  apply div_le_div_of_nonneg_right _ hk.le
  exact mul_le_mul_of_nonneg_right h2 he
end PositivityTheory.RgJS.DiagonalEntryNormBounds
