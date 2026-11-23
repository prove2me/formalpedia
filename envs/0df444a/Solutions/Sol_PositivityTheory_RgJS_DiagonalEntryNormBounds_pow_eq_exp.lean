-- Prove2me | solution 1 for PositivityTheory.RgJS.DiagonalEntryNormBounds.pow_eq_exp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:08:48.383798+00:00
-- url     : https://prove2.me/submissions/a04bfa0a-ad64-4291-a1f9-c4a39ce223d4

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_NewtonLow
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_DiagonalTermNorms_ConvergenceOfLandauEuler

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
theorem _root_.solution (hq : ∀ w, 2 ≤ q w) (σ : ℝ) (p : W × ℕ) :
    ((q p.1 : ℝ) ^ (-σ)) ^ (p.2 + 1) = Real.exp (-(ll q p * σ)) := by
  have h0 : (0 : ℝ) < q p.1 := by exact_mod_cast (lt_of_lt_of_le (by norm_num) (hq p.1))
  rw [← Real.rpow_natCast, ← Real.rpow_mul h0.le, Real.rpow_def_of_pos h0]
  unfold ll
  congr 1
  push_cast
  ring
end PositivityTheory.RgJS.DiagonalEntryNormBounds
