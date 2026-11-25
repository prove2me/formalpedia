-- Prove2me | solution 1 for P2M_PositivityTheory_RgJS_DirichletSeriesUnbounded__cpow_pow_b5c538feaa66
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:47:39.982823+00:00
-- url     : https://prove2.me/submissions/6094ecee-d65c-4c57-8963-f7a221da1f44

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_NewtonLow
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_NonnegativeCoefficients_DirichletSeriesUnbounded

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
open PositivityTheory.RgJS.DirichletSeriesUnbounded₂
variable {W X : Type} (q : W → ℕ) {d : X → ℕ} (A : ∀ x, W → Fin (d x) → ℂ) {ι : Type} [Fintype ι] (x : ι → X)
namespace PositivityTheory.RgJS.DirichletSeriesUnbounded₂
theorem _root_.solution (hq : ∀ w, (0 : ℝ) < q w) (σ : ℝ) (p : W × ℕ) :
    ((q p.1 : ℂ) ^ (-(σ : ℂ))) ^ (p.2 + 1) = ((Real.exp (-(ll q p * σ)) : ℝ) : ℂ) := by
  have h1 : (q p.1 : ℂ) = ((q p.1 : ℝ) : ℂ) := by push_cast; rfl
  have h2 : (-(σ : ℂ)) = ((-σ : ℝ) : ℂ) := by push_cast; ring
  rw [h1, h2, ← Complex.ofReal_cpow (hq p.1).le, ← Complex.ofReal_pow, Real.rpow_def_of_pos (hq p.1),
    ← Real.exp_nat_mul]
  congr 2
  simp only [ll]
  push_cast
  ring
end PositivityTheory.RgJS.DirichletSeriesUnbounded₂
