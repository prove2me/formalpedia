-- Prove2me | solution 6 for SensitivityCampaign.reach_215
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-24T08:28:04.029357+00:00
-- url     : https://prove2.me/submissions/0dc1b3b5-26f0-41cc-aa65-067415cca390
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_SensitivityProfileCycle_cofinal_215_certificates
import Theorems.Thm_SensitivityProfileCycle_finite_seeds
import Theorems.Thm_sensitivity_explicit_integer_amplification
import Theorems.Thm_SensitivityCampaign_finite_certificate_rational

open SensitivityCampaign SensitivityProfileCycle

private theorem rate_of_strict_gap (c : Certificate) (hR : 1 < c.radius)
    (p q : ℕ) (hq : 0 < q)
    (hgap : c.radius ^ p < (c.vertices ^ c.period) ^ q) :
    AchievesExponent ((p : ℝ) / (q : ℝ)) := by
  obtain ⟨C, hC, seeds⟩ := finite_seeds c
  let G := c.vertices ^ c.period
  let m := C ^ p * c.radius ^ p + 1
  have hRpos : 0 < c.radius := Nat.lt_trans Nat.zero_lt_one hR
  have hA : 1 < C * c.radius ^ m :=
    Nat.lt_of_lt_of_le hC (Nat.le_mul_of_pos_right C (Nat.pow_pos hRpos))
  have hG : 1 < G := Nat.one_lt_pow (Nat.ne_of_gt c.period_pos) c.vertices_gt_one
  have hB : 1 < G ^ m := Nat.one_lt_pow (Nat.succ_ne_zero _) hG
  obtain ⟨n, f, hs, hb⟩ := seeds m
  exact finite_certificate_rational f (fun _ => false) (C * c.radius ^ m) (G ^ m)
    p q hA hB hq hs hb
    (sensitivity_explicit_integer_amplification C c.radius G p q hRpos hgap).le

theorem solution : SensitivityCampaign.AchievesExponent (2.15 : ℝ) := by
  intro ε hε S hS
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  obtain ⟨c, hR, hbound⟩ := SensitivityProfileCycle.cofinal_215_certificates k
  let p := 43 * k + 41
  let q := 20 * (k + 1)
  have hgap : c.radius ^ p < (c.vertices ^ c.period) ^ q :=
    Nat.lt_of_lt_of_le (Nat.pow_lt_pow_right hR (show p < 43 * k + 42 by
      dsimp [p]
      omega)) hbound
  have hq : 0 < q := by
    dsimp [q]
    omega
  have hrate := rate_of_strict_gap c hR p q hq hgap
  have hkpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hscale : 1 < ε * ((k : ℝ) + 1) := (div_lt_iff₀ hkpos).mp hk
  have hclose : (2.15 : ℝ) - ε < (p : ℝ) / (q : ℝ) := by
    have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
    rw [show (2.15 : ℝ) = 43 / 20 by norm_num, lt_div_iff₀ hqpos]
    dsimp [p, q]
    push_cast
    nlinarith only [hscale]
  let r : ℝ := (p : ℝ) / (q : ℝ)
  obtain ⟨n, f, hs, hb⟩ := hrate (r - (2.15 - ε)) (sub_pos.mpr hclose) S hS
  refine ⟨n, f, hs, ?_⟩
  change (_ : ℝ) ^ (r - (r - (2.15 - ε))) ≤ _ at hb
  simpa only [sub_sub_cancel] using hb
