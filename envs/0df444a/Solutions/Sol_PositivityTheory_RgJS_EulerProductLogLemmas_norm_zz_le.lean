-- Prove2me | solution 1 for PositivityTheory.RgJS.EulerProductLogLemmas.norm_zz_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:08:48.461126+00:00
-- url     : https://prove2.me/submissions/9286a5c7-5e6a-4a57-b80e-2d9dbc5fbe41

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_NewtonLow
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_EulerLogarithms_EulerProductLogBound

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
open PositivityTheory.RgJS.EulerProductLogLemmas
variable {W : Type} {A B : Type} [Fintype A] [Fintype B]
omit [Fintype A] [Fintype B]
namespace PositivityTheory.RgJS.EulerProductLogLemmas
theorem _root_.solution {q : W → ℕ} {α : W → A → ℂ} {β : W → B → ℂ} {s : ℂ} (hq : ∀ w, 2 ≤ q w)
    (hα : ∀ w a, ‖α w a‖ ≤ Real.sqrt (q w)) (hβ : ∀ w b, ‖β w b‖ ≤ Real.sqrt (q w)) (w : W) (a : A) (b : B) :
    ‖zz q α β s w a b‖ ≤ (q w : ℝ) ^ (1 - s.re) := by
  have hq0 : (0 : ℝ) < q w := by have := hq w; positivity
  have hqn : 0 < q w := by have := hq w; omega
  rw [zz, norm_mul, norm_mul, Complex.norm_conj, Complex.norm_natCast_cpow_of_pos hqn, Complex.neg_re,
    sub_eq_add_neg, Real.rpow_add hq0, Real.rpow_one]
  refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hq0.le _)
  calc ‖α w a‖ * ‖β w b‖ ≤ Real.sqrt (q w) * Real.sqrt (q w) :=
        mul_le_mul (hα w a) (hβ w b) (norm_nonneg _) (Real.sqrt_nonneg _)
    _ = q w := Real.mul_self_sqrt hq0.le
end PositivityTheory.RgJS.EulerProductLogLemmas
