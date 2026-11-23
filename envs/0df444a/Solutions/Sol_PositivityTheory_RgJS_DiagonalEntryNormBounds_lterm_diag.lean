-- Prove2me | solution 1 for PositivityTheory.RgJS.DiagonalEntryNormBounds.lterm_diag
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:13:42.234832+00:00
-- url     : https://prove2.me/submissions/21ebe864-0f95-4482-873f-1fec7e76726a

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
theorem _root_.solution {A : Type} [Fintype A] (hq : ∀ w, 2 ≤ q w) (α : W → A → ℂ) (σ : ℝ) (p : W × ℕ) :
    lterm q α α σ p = ((cd α p * Real.exp (-(ll q p * σ)) : ℝ) : ℂ) := by
  have h0 : (0 : ℝ) < q p.1 := by exact_mod_cast (lt_of_lt_of_le (by norm_num) (hq p.1))
  unfold lterm cd
  have e1 : ((q p.1 : ℂ) ^ (-(σ : ℂ))) = (((q p.1 : ℝ) ^ (-σ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow h0.le]; push_cast; rfl
  rw [e1, ← Complex.ofReal_pow, pow_eq_exp q hq, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  ring
end PositivityTheory.RgJS.DiagonalEntryNormBounds
