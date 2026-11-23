-- Prove2me | solution 1 for PositivityTheory.RgJS.DiagonalEntryNormBounds.norm_lterm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:13:42.914071+00:00
-- url     : https://prove2.me/submissions/011532b5-3e70-4654-b035-9df5a3b45502

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_NewtonLow
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_DiagonalTermNorms_ConvergenceOfLandauEuler
import Theorems.Thm_PositivityTheory_RgJS_DiagonalEntryNormBounds_pow_eq_exp

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
theorem _root_.solution {A B : Type} [Fintype A] [Fintype B] (hq : ∀ w, 2 ≤ q w) (α : W → A → ℂ) (β : W → B → ℂ) (σ : ℝ)
    (p : W × ℕ) :
    ‖lterm q α β σ p‖ = ‖∑ a, α p.1 a ^ (p.2 + 1)‖ * ‖∑ b, β p.1 b ^ (p.2 + 1)‖ * Real.exp (-(ll q p * σ)) /
      ((p.2 : ℝ) + 1) := by
  have h0 : 0 < q p.1 := lt_of_lt_of_le (by norm_num) (hq p.1)
  unfold lterm
  rw [norm_div, norm_mul, norm_mul, Complex.norm_conj, norm_pow, Complex.norm_natCast_cpow_of_pos h0, ← pow_eq_exp q hq]
  have hd : ‖((p.2 : ℂ) + 1)‖ = (p.2 : ℝ) + 1 := by
    have : ((p.2 : ℂ) + 1) = (((p.2 : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hre : (-(σ : ℂ)).re = -σ := by simp
  rw [hre, hd]
end PositivityTheory.RgJS.DiagonalEntryNormBounds
