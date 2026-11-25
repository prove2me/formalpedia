-- Prove2me | solution 1 for PI.EF.PK.perronL_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:41:04.539472+00:00
-- url     : https://prove2.me/submissions/2114382d-3a7c-427c-960e-abe06a2e4808

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_PerronTruncOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_PerronLOf
import Theorems.Thm_PI_EF_PK_LSeries_twist_eq_neg_logDeriv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.EF PI.EF.PK
open Complex MeasureTheory intervalIntegral Real ArithmeticFunction LSeries
namespace PI.EF.PK
theorem _root_.solution {C : ℝ} (hC : 0 ≤ C) (h : PerronTrunc C) : PerronL C := by
  unfold PerronL psiRaw vertInt Err
  intro N _ χ u T T' hT hTu hTT' hT'
  have hu : 2 ≤ u := le_trans hT hTu
  have hc : 1 < cLine u := by
    unfold cLine
    have hlog := Real.log_pos (show (1:ℝ) < u by linarith)
    first
      | (have := one_div_pos.mpr hlog; linarith)
      | (norm_num; positivity)
      | done
  have hΛ : ∀ n : ℕ, ‖((Λ n : ℝ) : ℂ) * χ (n : ZMod N)‖ ≤ Λ n := by
    intro n
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    exact mul_le_of_le_one_right ArithmeticFunction.vonMangoldt_nonneg (DirichletCharacter.norm_le_one χ _)
  have key := h (fun n : ℕ => ((Λ n : ℝ) : ℂ) * χ (n : ZMod N)) hΛ u T' hu (by linarith)
  have hint : ∀ t : ℝ, LSeries (fun n : ℕ => ((Λ n : ℝ) : ℂ) * χ (n : ZMod N)) (↑(cLine u) + ↑t * I) =
      -logDeriv (DirichletCharacter.LFunction χ) (↑(cLine u) + ↑t * I) := by
    intro t
    apply LSeries_twist_eq_neg_logDeriv
    simpa using hc
  simp only [hint] at key
  refine key.trans ?_
  have hN : (1:ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hu0 : 0 < u := by linarith
  have hT0 : 0 < T := by linarith
  have hl0 : 0 ≤ Real.log u := Real.log_nonneg (by linarith)
  have h1 : u ≤ N * u := le_mul_of_one_le_left hu0.le hN
  have h2 : N * u ≤ N * u * T := le_mul_of_one_le_right (by positivity) (by linarith)
  have hl1 : Real.log u ≤ Real.log (N * u * T) := Real.log_le_log hu0 (h1.trans h2)
  have hl2 : Real.log u ≤ Real.log (N * u) := Real.log_le_log hu0 h1
  have hsq : Real.log u ^ 2 ≤ Real.log (N * u * T) ^ 2 := by nlinarith
  have hA : u * Real.log u ^ 2 / T' ≤ u * Real.log (N * u * T) ^ 2 / T := by
    calc u * Real.log u ^ 2 / T' ≤ u * Real.log u ^ 2 / T :=
          div_le_div_of_nonneg_left (by positivity) hT0 hTT'
      _ ≤ u * Real.log (N * u * T) ^ 2 / T :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hu0.le) hT0.le
  exact mul_le_mul_of_nonneg_left (add_le_add hA hl2) hC
end PI.EF.PK
