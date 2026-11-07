-- Prove2me | solution 1 for SensitivityCampaign.reach_213981365
-- status  : ACCEPTED   (prove)
-- author  : @dmilosch
-- created : 2026-11-06T23:40:22.354657+00:00
-- url     : https://prove2.me/submissions/235a7781-0233-4d58-a08b-4b1cc918be52

import Theorems.Thm_Sensitivity213981_actual_seeds
import Theorems.Thm_SensitivityCampaign_finite_certificate

/-!
Sharper numerical extraction from the already proved twenty-two-level seed
family of Sensitivity213981.actual_seeds. The seed construction and its
published bounds are unchanged. The limiting rate exceeds 2.13981365.

The growth argument adapts SensitivityProfileCycleGrowth.achieves_strict from
the existing 2.15 reduction, whose source attributes the logarithmic argument
to Prove2Me submission a9d25c46-43bd-4fb1-826b-0ed075b8cf0a, yousofy with Codex.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

namespace SensitivityImprovement215
open OAI.Paper320

theorem achieves_of_seed_bounds (c r g : ℕ) (β : ℝ)
    (hc : 1 < c) (hr : 1 < r) (hg : 1 < g) (hβ : 0 ≤ β)
    (hstrict : β < Real.log (g : ℝ) / Real.log (r : ℝ))
    (hseed : ∀ m : ℕ, ∃ (n : ℕ) (f : (Fin n → Bool) → Bool),
      sensitivity f ≤ c * r ^ m ∧ g ^ m ≤ blockSensitivity f) :
    SensitivityCampaign.AchievesExponent β := by
  classical
  have hcp : (0 : ℝ) < c := by exact_mod_cast (by omega : 0 < c)
  have hr1 : (1 : ℝ) < r := by exact_mod_cast hr
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
  obtain ⟨x, _, hx⟩ := Finset.exists_mem_eq_sup
    (Finset.univ : Finset (Fin n → Bool)) Finset.univ_nonempty (blockSensitivityAt f)
  have hsup : blockSensitivity f =
      (Finset.univ : Finset (Fin n → Bool)).sup (blockSensitivityAt f) := by
    unfold blockSensitivity
    congr 1
    ext y
    simp
  have hbx : g^m ≤ blockSensitivityAt f x := by
    exact hb.trans_eq (hsup.trans hx)
  have hA : 1 < c * r ^ m :=
    hc.trans_le (Nat.le_mul_of_pos_right c (pow_pos (by omega : 0 < r) m))
  have hB : 1 < g ^ m := one_lt_pow₀ hg (Nat.ne_of_gt hmpos)
  apply SensitivityCampaign.finite_certificate f x
    (c * r ^ m) (g ^ m) β hA hB hβ hs hbx
  have hrp : (0 : ℝ) < r := by linarith
  have hp : (0 : ℝ) < (c * r ^ m : ℕ) := by
    exact_mod_cast (by omega : 0 < c * r ^ m)
  have hbp : (0 : ℝ) < (g ^ m : ℕ) := by
    exact_mod_cast (by omega : 0 < g ^ m)
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

theorem power_gap_37665_17602 :
    (10121928 : ℕ)^37665 < (5591^4)^17602 := by
  rw [← pow_mul]
  change (10121928 : ℕ)^37665 < 5591^70408
  decide +kernel

theorem reaches_213981365 :
    SensitivityCampaign.AchievesExponent (213981365 / 100000000 : ℝ) := by
  have hratio := rational_lt_rate_of_pow_lt (5591^4) 10121928 37665 17602
    (by norm_num) (by norm_num) (by norm_num) power_gap_37665_17602
  have hstrict : (213981365 / 100000000 : ℝ) <
      Real.log (5591^4 : ℕ) / Real.log (10121928 : ℝ) :=
    lt_trans (by norm_num : (213981365 / 100000000 : ℝ) < 37665/17602) hratio
  apply achieves_of_seed_bounds (10^15) 10121928 (5591^4)
    (213981365 / 100000000 : ℝ) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hstrict
  intro m
  obtain ⟨n, f, _, hs, hb⟩ := Sensitivity213981.actual_seeds m
  exact ⟨n, f, hs, hb⟩

end SensitivityImprovement215

theorem solution :
    SensitivityCampaign.AchievesExponent (213981365 / 100000000 : ℝ) :=
  SensitivityImprovement215.reaches_213981365

#print axioms solution
