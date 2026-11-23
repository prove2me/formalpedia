-- Prove2me | solution 1 for PositivityTheory.RgJS.DiagonalEntryNormBounds.norm_lterm_diag
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:15:53.6614+00:00
-- url     : https://prove2.me/submissions/f0c33b62-caf5-4f53-b792-8025e4abf6f0

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_NewtonLow
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_DiagonalTermNorms_ConvergenceOfLandauEuler
import Theorems.Thm_PositivityTheory_RgJS_DiagonalEntryNormBounds_cd_nonneg
import Theorems.Thm_PositivityTheory_RgJS_DiagonalEntryNormBounds_lterm_diag

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
theorem _root_.solution {A : Type} [Fintype A] (hq : ∀ w, 2 ≤ q w) (α : W → A → ℂ) (σ : ℝ) (p : W × ℕ) :
    ‖lterm q α α σ p‖ = cd α p * Real.exp (-(ll q p * σ)) := by
  rw [lterm_diag q hq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
  exact mul_nonneg (cd_nonneg α p) (Real.exp_pos _).le
end PositivityTheory.RgJS.DiagonalEntryNormBounds
