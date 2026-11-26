-- Prove2me | solution 1 for Sendov.polar_origin_incompatible
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T20:30:25.824574+00:00
-- url     : https://prove2.me/submissions/16ec91f9-e5ba-4756-b21e-55c6df80f364

import Definitions.Def_Sendov_Reduction_Alpha17
import Definitions.Def_Sendov_Main
import Definitions.Def_Sendov_Reduction_Main
import Theorems.Thm_Sendov_QQ_nonneg
import Theorems.Thm_Sendov_alpha_le_seventeen
import Theorems.Thm_Sendov_alpha_pos
import Theorems.Thm_Sendov_beta_le
import Theorems.Thm_Sendov_feasible_of_beta
import Theorems.Thm_Sendov_log_le_alpha_mul
import Theorems.Thm_Sendov_one_le_of_origin
import Theorems.Thm_Sendov_polar_exp
import Theorems.Thm_Sendov_stat_lt_one
import Theorems.Thm_Sendov_stat_of_one_le


set_option autoImplicit false
open Sendov
open MeasureTheory
namespace Sendov
theorem _root_.solution {n : ℕ} (hn : 5 ≤ n) {a x α : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hx : x ^ 2 ≤ 1)
    (hα : α = M n * (1 - a ^ 2) / 2)
    (hpolar : 1 ≤ ∫ t in (0 : ℝ)..1, Ppolar a x t ^ (((n : ℝ) - 1) / 2))
    (horigin : 2 * α + a * x ≤ (1 - x ^ 2) / (2 * M n)
      + a ^ 2 * n * M n * ∫ t in (0 : ℝ)..1, t * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2)) :
    False := by
  have hn2 : 2 ≤ n := by omega
  have hα0 : 0 < α := alpha_pos hn2 ha1 ha.le hα
  have h3 : (0 : ℝ) < 3 + α := by linarith
  have hfeas : (a * x) ^ 2 ≤ a ^ 2 := by nlinarith [sq_nonneg a, sq_nonneg x]
  have hB0 : 0 ≤ QQ (a * x) (a ^ 2) 1 := QQ_nonneg hfeas 1
  -- `(1Q) ⟹ (lt) ⟹ (beta-bound)`, both halves
  have hlt := polar_exp hn2 hx hα hpolar
  have hbeta : QQ (a * x) (a ^ 2) 1 ≤ α / (3 + α) := beta_le hα0 hB0 hlt
  have hB1lt : QQ (a * x) (a ^ 2) 1 < 1 := by
    have : α / (3 + α) < 1 := by rw [div_lt_one h3]; linarith
    linarith
  have hlogb : Real.log α ≤ α * (1 - QQ (a * x) (a ^ 2) 1) :=
    log_le_alpha_mul hα0 hB1lt.le hlt
  -- `α ≤ 17`
  have h17 : α ≤ 17 := alpha_le_seventeen hn ha ha1 hx hα hbeta hlogb horigin
  -- `(origin-exact) ⟹ (1le) ⟹ stat`
  have h1le := one_le_of_origin hn ha ha1 hx hα hα0 hB1lt horigin
  have hstat : 1 ≤ R n α := stat_of_one_le hn hx hα hα0 hbeta h1le
  -- but `stat` is false
  exact absurd hstat
    (not_le.2 (stat_lt_one hn hα0.le h17 (feasible_of_beta hn2 hx hα hα0 hbeta)))
end Sendov
