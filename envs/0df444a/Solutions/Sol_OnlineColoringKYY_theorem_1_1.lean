-- Prove2me | solution 1 for OnlineColoringKYY.theorem_1_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T11:07:45.94049+00:00
-- url     : https://prove2.me/submissions/44318a32-5d7d-4ab5-9f4b-e3800a4b54bf

import Mathlib
import Definitions.Def_OnlineColoringKYY_OnlineColoringAlg
import Definitions.Def_OnlineColoringKYY_prefixGraph
import Definitions.Def_OnlineColoringKYY_run
import Definitions.Def_OnlineColoringKYY_IsProper
import Definitions.Def_OnlineColoringKYY_numColors
import Theorems.Thm_OnlineColoringKYY_theorem_1_1_witness_bound

section
set_option autoImplicit false

namespace OnlineColoringKYY

theorem chk_theorem_1_1 :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ A : OnlineColoringAlg, IsProper A →
      ∃ G : SimpleGraph (Fin n), ∃ k : ℕ, G.Colorable k ∧
        c * ((n : ℝ) / Real.logb 2 n) * (k : ℝ) ≤ (numColors A G : ℝ) := by
  refine ⟨1 / 8, by norm_num, 2, fun n hn A hA => ?_⟩
  obtain ⟨G, hG, hc⟩ := OnlineColoringKYY.theorem_1_1_witness_bound n hn A hA
  refine ⟨G, 2 * Nat.clog 2 n, hG, ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlog1 : 1 ≤ Real.logb 2 n := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) hn0]
    simpa using (by exact_mod_cast hn : (2 : ℝ) ≤ n)
  -- clog - 1 < logb 2 n
  have hcl : ((Nat.clog 2 n : ℕ) : ℝ) ≤ 2 * Real.logb 2 n := by
    have hpos : 1 ≤ Nat.clog 2 n := Nat.clog_pos (by norm_num) hn
    have hlt : 2 ^ (Nat.clog 2 n - 1) < n := Nat.pow_pred_clog_lt_self (by norm_num) (by omega)
    have h1 : ((Nat.clog 2 n - 1 : ℕ) : ℝ) < Real.logb 2 n := by
      rw [Real.lt_logb_iff_rpow_lt (by norm_num) hn0]
      rw [Real.rpow_natCast]
      exact_mod_cast hlt
    have h2 : ((Nat.clog 2 n - 1 : ℕ) : ℝ) = (Nat.clog 2 n : ℝ) - 1 := by
      rw [Nat.cast_sub hpos]; simp
    linarith
  have hnc : (n : ℝ) ≤ 2 * (numColors A G : ℝ) := by exact_mod_cast hc
  have hl0 : 0 < Real.logb 2 n := by linarith
  have : (1 / 8 : ℝ) * ((n : ℝ) / Real.logb 2 n) * (((2 * Nat.clog 2 n : ℕ) : ℝ)) ≤ (n : ℝ) / 2 := by
    push_cast
    rw [show (1 / 8 : ℝ) * ((n : ℝ) / Real.logb 2 n) * (2 * (Nat.clog 2 n : ℝ)) =
      ((n : ℝ) * (Nat.clog 2 n : ℝ)) / (4 * Real.logb 2 n) by field_simp; ring]
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right hcl hn0.le]
  linarith

end OnlineColoringKYY
end

theorem solution : type_of% @OnlineColoringKYY.chk_theorem_1_1 := @OnlineColoringKYY.chk_theorem_1_1
