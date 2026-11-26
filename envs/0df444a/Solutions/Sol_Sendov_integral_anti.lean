-- Prove2me | solution 1 for Sendov.integral_anti
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:08:30.70226+00:00
-- url     : https://prove2.me/submissions/c51732ed-373c-43c3-95ad-ab06bebacafa

import Definitions.Def_Sendov_Common_Rpow
import Definitions.Def_Sendov_FiniteRange_Batch
import Theorems.Thm_Sendov_Q_anti
import Theorems.Thm_P2M_Sendov_rpow_le_rpow_exponent_ge__9a7132cbe0b0
import Theorems.Thm_Sendov_Q_le_one
import Theorems.Thm_Sendov_Q_nonneg
import Theorems.Thm_Sendov_continuous_integrand


set_option autoImplicit false
open Sendov
variable {α t : ℝ}
open MeasureTheory
namespace Sendov
theorem _root_.solution {m n : ℕ} (hm : 5 ≤ m) (h : m ≤ n) (hα : 0 ≤ α)
    (hcm : 0 ≤ c m α) (hfn : c n α ^ 2 ≤ A n α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q n α t ^ (((n : ℝ) - 4) / 2))
      ≤ ∫ t in (0 : ℝ)..1, t ^ 3 * Q m α t ^ (((m : ℝ) - 4) / 2) := by
  have hm2 : 2 ≤ m := by omega
  have hn2 : 2 ≤ n := by omega
  have hmR : (5 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmnR : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
  have hem : (0 : ℝ) < ((m : ℝ) - 4) / 2 := by linarith
  have hen : (0 : ℝ) ≤ ((n : ℝ) - 4) / 2 := by linarith
  refine intervalIntegral.integral_mono_on (by norm_num)
    ((continuous_integrand n α hen).intervalIntegrable _ _)
    ((continuous_integrand m α hem.le).intervalIntegrable _ _) ?_
  intro t ht
  obtain ⟨ht0, ht1⟩ := ht
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg ht0 3)
  have hQn : 0 ≤ Q n α t := Q_nonneg hfn t
  have hmono : Q n α t ≤ Q m α t := Q_anti hm2 h hα ht0 ht1
  -- nonnegativity at `m` comes free from monotonicity, so feasibility at `m` is not needed
  have hQm0 : 0 ≤ Q m α t := le_trans hQn hmono
  have hQm1 : Q m α t ≤ 1 := Q_le_one hm2 hα hcm ht0 ht1
  have hstep1 : Q n α t ^ (((n : ℝ) - 4) / 2) ≤ Q m α t ^ (((n : ℝ) - 4) / 2) :=
    Real.rpow_le_rpow hQn hmono hen
  have hstep2 : Q m α t ^ (((n : ℝ) - 4) / 2) ≤ Q m α t ^ (((m : ℝ) - 4) / 2) :=
    rpow_le_rpow_exponent_ge' hQm0 hQm1 hem (by linarith)
  linarith
end Sendov
