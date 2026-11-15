-- Prove2me | solution 3 for SensitivityCampaign.reach_215
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @spongeboi
-- created : 2026-11-14T08:38:29.915631+00:00
-- url     : https://prove2.me/submissions/52f31648-163a-4b21-8f5a-cf32c5f7518e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_sensitivity_explicit_integer_amplification
import Theorems.Thm_SensitivityProfileCycle_exists_215_certificate
import Theorems.Thm_SensitivityProfileCycle_finite_seeds
import Theorems.Thm_SensitivityCampaign_finite_certificate

set_option autoImplicit false
set_option maxHeartbeats 2000000

open OAI.Paper320

theorem solution : SensitivityCampaign.AchievesExponent (2.15 : ℝ) := by
  obtain ⟨c, hr, hpow⟩ := SensitivityProfileCycle.exists_215_certificate
  obtain ⟨C, hC, hseed⟩ := SensitivityProfileCycle.finite_seeds c
  let G := c.vertices ^ c.period
  let m := C ^ 43 * c.radius ^ 43 + 1
  have hm : 0 < m := by dsimp [m]; omega
  have hG : 1 < G :=
    one_lt_pow₀ c.vertices_gt_one (Nat.ne_of_gt c.period_pos)
  obtain ⟨n, f, hs, hb⟩ := hseed m
  have hinteger := sensitivity_explicit_integer_amplification
    C c.radius G 43 20 (by omega) hpow
  change (C * c.radius ^ m) ^ 43 < (G ^ m) ^ 20 at hinteger
  have hA : 1 < C * c.radius ^ m :=
    hC.trans_le (Nat.le_mul_of_pos_right C (pow_pos (by omega : 0 < c.radius) m))
  have hB : 1 < G ^ m := one_lt_pow₀ hG (Nat.ne_of_gt hm)
  apply SensitivityCampaign.finite_certificate f (fun _ => false)
    (C * c.radius ^ m) (G ^ m) (2.15 : ℝ) hA hB (by norm_num) hs hb
  have hAp : (0 : ℝ) < (C * c.radius ^ m : ℕ) := by
    exact_mod_cast (by omega : 0 < C * c.radius ^ m)
  have hBp : (0 : ℝ) < (G ^ m : ℕ) := by
    exact_mod_cast (by omega : 0 < G ^ m)
  apply (Real.rpow_le_iff_le_log hAp hBp).2
  have hp : ((C * c.radius ^ m : ℕ) : ℝ) ^ 43 < ((G ^ m : ℕ) : ℝ) ^ 20 := by
    exact_mod_cast hinteger
  have hlogs := Real.log_lt_log (pow_pos hAp 43) hp
  rw [Real.log_pow, Real.log_pow] at hlogs
  norm_num at hlogs ⊢
  nlinarith
