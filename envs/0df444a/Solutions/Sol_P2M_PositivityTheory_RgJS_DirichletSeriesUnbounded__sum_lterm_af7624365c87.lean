-- Prove2me | solution 1 for P2M_PositivityTheory_RgJS_DirichletSeriesUnbounded__sum_lterm_af7624365c87
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:55:53.227676+00:00
-- url     : https://prove2.me/submissions/e869594e-078f-40f1-af4c-1187a9d2a937

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_NewtonLow
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_NonnegativeCoefficients_DirichletSeriesUnbounded
import Theorems.Thm_P2M_PositivityTheory_RgJS_DirichletSeriesUnbounded__cpow_pow_b5c538feaa66

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
    ∑ i, ∑ j, lterm q (A (x i)) (A (x j)) σ p = ((cc A x p * Real.exp (-(ll q p * σ)) : ℝ) : ℂ) := by
  set s : ι → ℂ := fun i => ∑ a, A (x i) p.1 a ^ (p.2 + 1) with hs
  set z : ℂ := ((q p.1 : ℂ) ^ (-(σ : ℂ))) ^ (p.2 + 1) / ((p.2 : ℂ) + 1) with hz
  have e1 : ∀ i j, lterm q (A (x i)) (A (x j)) σ p = s i * conj (s j) * z := by
    intro i j
    simp only [lterm, hs, hz]
    ring
  simp only [e1]
  have e2 : ∑ i, ∑ j, s i * conj (s j) * z = (∑ i, s i) * conj (∑ j, s j) * z := by
    rw [map_sum, Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
  rw [e2, Complex.mul_conj, Complex.normSq_eq_norm_sq, hz, cpow_pow q hq σ p]
  simp only [cc, PP, hs]
  push_cast
  ring
end PositivityTheory.RgJS.DirichletSeriesUnbounded₂
