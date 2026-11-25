-- Prove2me | solution 1 for PositivityTheory.RgJS.EulerProductLogLemmas.norm_lterm_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:55:59.143799+00:00
-- url     : https://prove2.me/submissions/77606d08-0212-4ea8-ae8d-fc590022b1af

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_NewtonLow
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_EulerLogarithms_EulerProductLogBound
import Theorems.Thm_PositivityTheory_RgJS_EulerProductLogLemmas_lterm_eq
import Theorems.Thm_PositivityTheory_RgJS_EulerProductLogLemmas_norm_zz_le

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
namespace PositivityTheory.RgJS.EulerProductLogLemmas
theorem _root_.solution {q : W → ℕ} {α : W → A → ℂ} {β : W → B → ℂ} {s : ℂ} (hq : ∀ w, 2 ≤ q w)
    (hα : ∀ w a, ‖α w a‖ ≤ Real.sqrt (q w)) (hβ : ∀ w b, ‖β w b‖ ≤ Real.sqrt (q w)) (p : W × ℕ) :
    ‖lterm q α β s p‖ ≤ maj q s (Fintype.card A * Fintype.card B) p := by
  rw [lterm_eq, maj]
  have hd : (1 : ℝ) ≤ ‖((p.2 : ℂ) + 1)‖ := by
    have : ((p.2 : ℂ) + 1) = ((p.2 + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_natCast]
    exact_mod_cast Nat.succ_pos _
  have hterm : ∀ a b, ‖zz q α β s p.1 a b ^ (p.2 + 1) / ((p.2 : ℂ) + 1)‖ ≤ ((q p.1 : ℝ) ^ (1 - s.re)) ^ (p.2 + 1) := by
    intro a b
    rw [norm_div, norm_pow]
    refine (div_le_self (pow_nonneg (norm_nonneg _) _) hd).trans ?_
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_zz_le hq hα hβ p.1 a b) _
  calc ‖∑ a, ∑ b, zz q α β s p.1 a b ^ (p.2 + 1) / ((p.2 : ℂ) + 1)‖
      ≤ ∑ a : A, ∑ b : B, ((q p.1 : ℝ) ^ (1 - s.re)) ^ (p.2 + 1) :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => (norm_sum_le _ _).trans
          (Finset.sum_le_sum fun b _ => hterm a b))
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
end PositivityTheory.RgJS.EulerProductLogLemmas
