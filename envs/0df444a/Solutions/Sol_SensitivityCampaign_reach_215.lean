-- Prove2me | solution 1 for SensitivityCampaign.reach_215
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dmilosch
-- created : 2026-10-21T21:26:46.824504+00:00
-- url     : https://prove2.me/submissions/de8328d7-41ea-4f05-b8d2-36de4c1eec70
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_SensitivityProfileCycle_exists_215_certificate
import Theorems.Thm_SensitivityProfileCycle_finite_seeds
import Theorems.Thm_SensitivityCampaign_finite_certificate

set_option autoImplicit false
set_option maxHeartbeats 2000000
/- Growth-rate argument adapted, with attribution, from the accepted source
   Prove2Me submission a9d25c46-43bd-4fb1-826b-0ed075b8cf0a,
   namespace SensitivityPeriodicLog, by yousofy with Codex (2026-10-21).
   It uses the campaign's existing finite-certificate theorem. -/

namespace SensitivityProfileCycleGrowth

open OAI.Paper320

theorem achieves_strict (c r g : ℕ) (β : ℝ)
    (hc : 1 < c) (hr : 1 < r) (hg : 1 < g) (hβ : 0 ≤ β)
    (hstrict : β < Real.log (g : ℝ) / Real.log (r : ℝ))
    (hseed : ∀ m : ℕ, ∃ (n : ℕ) (f : (Fin n → Bool) → Bool),
      sensitivity f ≤ c * r ^ m ∧ g ^ m ≤ blockSensitivityAt f (fun _ => false)) :
    SensitivityCampaign.AchievesExponent β := by
  have hcp : (0 : ℝ) < c := by exact_mod_cast (by omega : 0 < c)
  have hr1 : (1 : ℝ) < r := by exact_mod_cast hr
  have hgp : (0 : ℝ) < g := by exact_mod_cast (by omega : 0 < g)
  have hlr : 0 < Real.log (r : ℝ) := Real.log_pos hr1
  have hgap : 0 < Real.log (g : ℝ) - β * Real.log (r : ℝ) := by
    have hh := (lt_div_iff₀ hlr).mp hstrict
    linarith
  let δ := Real.log (g : ℝ) - β * Real.log (r : ℝ)
  obtain ⟨m, hm⟩ := exists_nat_gt (max 0 (β * Real.log (c : ℝ) / δ))
  have hmposr : (0 : ℝ) < m := (le_max_left _ _).trans_lt hm
  have hmpos : 0 < m := by exact_mod_cast hmposr
  have hmul : β * Real.log (c : ℝ) < (m : ℝ) * δ :=
    (div_lt_iff₀ hgap).mp ((le_max_right _ _).trans_lt hm)
  obtain ⟨n, f, hs, hb⟩ := hseed m
  have hA : 1 < c * r ^ m :=
    hc.trans_le (Nat.le_mul_of_pos_right c (pow_pos (by omega : 0 < r) m))
  have hB : 1 < g ^ m := one_lt_pow₀ hg (Nat.ne_of_gt hmpos)
  apply SensitivityCampaign.finite_certificate f (fun _ => false)
    (c * r ^ m) (g ^ m) β hA hB hβ hs hb
  have hrp : (0 : ℝ) < r := by linarith
  have hp : (0 : ℝ) < (c * r ^ m : ℕ) := by exact_mod_cast (by omega : 0 < c * r ^ m)
  have hbp : (0 : ℝ) < (g ^ m : ℕ) := by exact_mod_cast (by omega : 0 < g ^ m)
  apply (Real.rpow_le_iff_le_log hp hbp).2
  push_cast
  rw [Real.log_mul (ne_of_gt hcp) (ne_of_gt (pow_pos hrp m)),
    Real.log_pow, Real.log_pow]
  dsimp only [δ] at hmul
  nlinarith

theorem rational_lt_rate_of_pow_lt (g r p q : ℕ)
    (hg : 1 < g) (hr : 1 < r) (hq : 0 < q)
    (hpow : r^p < g^q) :
    (p : ℝ) / (q : ℝ) < Real.log (g : ℝ) / Real.log (r : ℝ) := by
  have hrp : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hr1 : (1 : ℝ) < r := by exact_mod_cast hr
  have hqp : (0 : ℝ) < q := by exact_mod_cast hq
  have hpowr : (r : ℝ)^p < (g : ℝ)^q := by exact_mod_cast hpow
  have hlogs := Real.log_lt_log (pow_pos hrp p) hpowr
  rw [Real.log_pow, Real.log_pow] at hlogs
  apply (div_lt_div_iff₀ hqp (Real.log_pos hr1)).2
  nlinarith

end SensitivityProfileCycleGrowth

/-- The only unproved input is the explicitly finite profile-cycle certificate. -/
theorem solution : SensitivityCampaign.AchievesExponent (2.15 : ℝ) := by
  obtain ⟨c, hr, hpow⟩ := SensitivityProfileCycle.exists_215_certificate
  obtain ⟨C, hC, hseed⟩ := SensitivityProfileCycle.finite_seeds c
  have hg : 1 < c.vertices ^ c.period :=
    one_lt_pow₀ c.vertices_gt_one (Nat.ne_of_gt c.period_pos)
  have hgap := SensitivityProfileCycleGrowth.rational_lt_rate_of_pow_lt
    (c.vertices ^ c.period) c.radius 43 20 hg hr (by norm_num) hpow
  have hgap' : (2.15 : ℝ) <
      Real.log (c.vertices ^ c.period : ℕ) / Real.log (c.radius : ℝ) := by
    norm_num at hgap ⊢
    exact hgap
  exact SensitivityProfileCycleGrowth.achieves_strict C c.radius
    (c.vertices ^ c.period) (2.15 : ℝ) hC hr hg (by norm_num) hgap' hseed