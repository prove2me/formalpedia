-- Prove2me | solution 1 for RealPinwheel.FiveSixths.bounded_density_base
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T03:17:52.302376+00:00
-- url     : https://prove2.me/submissions/4b3cd1f5-3eec-454c-82de-c4e3b938fda4

import Theorems.Thm_RealPinwheel_FiveSixths_density_certificate_1
import Theorems.Thm_RealPinwheel_FiveSixths_density_certificate_2
import Theorems.Thm_RealPinwheel_FiveSixths_density_certificate_3
import Theorems.Thm_RealPinwheel_FiveSixths_density_certificate_4
import Theorems.Thm_RealPinwheel_FiveSixths_density_certificate_5
import Theorems.Thm_RealPinwheel_FiveSixths_density_certificate_6
import Theorems.Thm_RealPinwheel_FiveSixths_density_certificate_7
import Theorems.Thm_RealPinwheel_FiveSixths_density_certificate_8

open RealPinwheel.FiveSixths

theorem solution {n : ℕ} (A : Instance n) (hn : n ≤ 8) (hD : density A ≤ (5 : ℝ) / 6) :
    ∃ (L : ℕ) (S : ℕ → Fin n), 0 < L ∧ L < 4 * 2 ^ n ∧
      (∀ t, S (t + L) = S t) ∧ Valid A.period S := by
  have hnpos := A.positive_dimension
  interval_cases n
  · obtain ⟨L, S, hL, hb, hp, hv⟩ := RealPinwheel.FiveSixths.density_certificate_1 A hD
    refine ⟨L, S, hL, ?_, hp, hv⟩
    norm_num
    omega
  · obtain ⟨L, S, hL, hb, hp, hv⟩ := RealPinwheel.FiveSixths.density_certificate_2 A hD
    refine ⟨L, S, hL, ?_, hp, hv⟩
    norm_num
    omega
  · obtain ⟨L, S, hL, hb, hp, hv⟩ := RealPinwheel.FiveSixths.density_certificate_3 A hD
    refine ⟨L, S, hL, ?_, hp, hv⟩
    norm_num
    omega
  · obtain ⟨L, S, hL, hb, hp, hv⟩ := RealPinwheel.FiveSixths.density_certificate_4 A hD
    refine ⟨L, S, hL, ?_, hp, hv⟩
    norm_num
    omega
  · obtain ⟨L, S, hL, hb, hp, hv⟩ := RealPinwheel.FiveSixths.density_certificate_5 A hD
    refine ⟨L, S, hL, ?_, hp, hv⟩
    norm_num
    omega
  · obtain ⟨L, S, hL, hb, hp, hv⟩ := RealPinwheel.FiveSixths.density_certificate_6 A hD
    refine ⟨L, S, hL, ?_, hp, hv⟩
    norm_num
    omega
  · obtain ⟨L, S, hL, hb, hp, hv⟩ := RealPinwheel.FiveSixths.density_certificate_7 A hD
    refine ⟨L, S, hL, ?_, hp, hv⟩
    norm_num
    omega
  · obtain ⟨L, S, hL, hb, hp, hv⟩ := RealPinwheel.FiveSixths.density_certificate_8 A hD
    refine ⟨L, S, hL, ?_, hp, hv⟩
    norm_num
    omega
