-- Prove2me | solution 1 for PositivityTheory.RgJS.DiagonalEntryNormBounds.norm_lterm_anti
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:54:36.324683+00:00
-- url     : https://prove2.me/submissions/b54b24cb-cfda-4c73-9d78-c31290781cf3

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_NewtonLow
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_DiagonalTermNorms_ConvergenceOfLandauEuler
import Theorems.Thm_PositivityTheory_RgJS_DiagonalEntryNormBounds_ll_nonneg
import Theorems.Thm_PositivityTheory_RgJS_DiagonalEntryNormBounds_norm_lterm

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
    {σ σ₁ : ℝ} (h : σ₁ ≤ σ) (p : W × ℕ) : ‖lterm q α β σ p‖ ≤ ‖lterm q α β σ₁ p‖ := by
  rw [norm_lterm q hq, norm_lterm q hq]
  have hk : (0 : ℝ) < (p.2 : ℝ) + 1 := by positivity
  apply div_le_div_of_nonneg_right _ hk.le
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.2
  have := ll_nonneg q hq p
  nlinarith
end PositivityTheory.RgJS.DiagonalEntryNormBounds
