-- Prove2me | solution 1 for PiIrrationality.mignotte_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-03T07:30:24.2866+00:00
-- url     : https://prove2.me/submissions/4ef47f77-a8fb-4b09-b368-0ca9318ee2bd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_PiIrrationality_mignotte_hermite_estimates
import Theorems.Thm_PiIrrationality_mignotte_parameter_selection
import Theorems.Thm_PiIrrationality_remainder_separation
import Definitions.Def_PiIrrationality_UpperBound
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false

namespace PiIrrationality

/-- Increasing an upper bound preserves the epsilon formulation. -/
theorem UpperBound.mono {A B : ℝ} (hA : UpperBound A) (hAB : A ≤ B) :
    UpperBound B := by
  intro ε hε
  obtain ⟨Q, hQ⟩ := hA ε hε
  refine ⟨Q, ?_⟩
  intro p q hq hQq
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hp := Real.rpow_le_rpow_of_exponent_le hq1 (show A + ε ≤ B + ε from by linarith)
  exact lt_of_le_of_lt (one_div_le_one_div_of_le (Real.rpow_pos_of_pos hq0 _) hp)
    (hQ p q hq hQq)

/-- An eventual non-strict power lower bound implies the epsilon formulation. -/
theorem upperBound_of_eventual_power_bound {B : ℝ}
    (hB : ∃ Q : ℕ, ∀ (p : ℤ) (q : ℕ), 0 < q → Q ≤ q →
      1 / (q : ℝ) ^ B ≤ |Real.pi - (p : ℝ) / (q : ℝ)|) :
    UpperBound B := by
  obtain ⟨Q, hQ⟩ := hB
  intro ε hε
  refine ⟨max Q 2, ?_⟩
  intro p q hq hQq
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hq2 : 2 ≤ q := le_trans (le_max_right Q 2) hQq
  have hq1 : (1 : ℝ) < q := by exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) hq2)
  have hp := Real.rpow_lt_rpow_of_exponent_lt hq1 (lt_add_of_pos_right B hε)
  exact lt_of_lt_of_le (one_div_lt_one_div_of_lt (Real.rpow_pos_of_pos hq0 _) hp)
    (hQ p q hq (le_trans (le_max_left Q 2) hQq))

/-- It suffices to bound approximations having positive numerator. -/
theorem upperBound_of_eventual_power_bound_pos {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∃ Q : ℕ, ∀ (p : ℤ) (q : ℕ), 0 < p → 0 < q → Q ≤ q →
      1 / (q : ℝ) ^ B ≤ |Real.pi - (p : ℝ) / (q : ℝ)|) :
    UpperBound B := by
  apply upperBound_of_eventual_power_bound
  obtain ⟨Q, hQ⟩ := hB
  refine ⟨Q, ?_⟩
  intro p q hq hQq
  by_cases hp : 0 < p
  · exact hQ p q hp hq hQq
  · have hp0 : (p : ℝ) ≤ 0 := by exact_mod_cast (le_of_not_gt hp)
    have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr hq
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
    have hrpow : 1 ≤ (q : ℝ) ^ B := Real.one_le_rpow hq1 hB0
    have hfrac : (p : ℝ) / (q : ℝ) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hp0 hq0.le
    have hrecip : 1 / (q : ℝ) ^ B ≤ 1 := (div_le_one (Real.rpow_pos_of_pos hq0 B)).mpr hrpow
    have habs : 1 ≤ |Real.pi - (p : ℝ) / (q : ℝ)| := by
      rw [abs_of_nonneg (by linarith [Real.pi_pos])]
      linarith [Real.two_le_pi]
    exact hrecip.trans habs

/-- For exponent 20, only positive approximations below 3.15 require an estimate. -/
theorem upperBound_twenty_of_eventual_near_power_bound
    (hB : ∃ Q : ℕ, ∀ (p : ℤ) (q : ℕ), 0 < p → 0 < q → Q ≤ q →
      (p : ℝ) / (q : ℝ) < 63 / 20 →
      1 / (q : ℝ) ^ (20 : ℝ) ≤ |Real.pi - (p : ℝ) / (q : ℝ)|) :
    UpperBound 20 := by
  apply upperBound_of_eventual_power_bound_pos (by norm_num)
  obtain ⟨Q, hQ⟩ := hB
  refine ⟨max Q 1000, ?_⟩
  intro p q hp hq hQq
  by_cases hnear : (p : ℝ) / (q : ℝ) < 63 / 20
  · exact hQ p q hp hq (le_trans (le_max_left Q 1000) hQq) hnear
  · have hq1000 : (1000 : ℝ) ≤ q := by
      exact_mod_cast (le_trans (le_max_right Q 1000) hQq)
    have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr hq
    have hpow : (q : ℝ) ≤ (q : ℝ) ^ (20 : ℝ) := by
      simpa using Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ q)
        (by norm_num : (1 : ℝ) ≤ 20)
    have hrecip : 1 / (q : ℝ) ^ (20 : ℝ) ≤ 1 / (1000 : ℝ) :=
      one_div_le_one_div_of_le (by norm_num) (hq1000.trans hpow)
    have hfar : 63 / 20 ≤ (p : ℝ) / (q : ℝ) := le_of_not_gt hnear
    have habs : 1 / (1000 : ℝ) ≤ |Real.pi - (p : ℝ) / (q : ℝ)| := by
      rw [abs_of_nonpos (by linarith [Real.pi_lt_d4])]
      linarith [Real.pi_lt_d4]
    exact hrecip.trans habs

end PiIrrationality

theorem mignotte_certificate_bridge (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hcertificate : ∃ R U T : ℂ,
      R - U = (((Real.pi - (p : ℝ) / (q : ℝ)) / 2 : ℝ) : ℂ) * Complex.I * T ∧
      1 / (32 * (q : ℝ)^5) ≤ ‖U‖ ∧
      ‖R‖ ≤ (1 / (32 * (q : ℝ)^5)) / 2 ∧
      ‖T‖ < (q : ℝ)^15 / 32) :
    1 / (q : ℝ)^20 < |Real.pi - (p : ℝ) / (q : ℝ)| := by
  obtain ⟨R, U, T, hid, hU, hR, hT⟩ := hcertificate
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hqne : (q : ℝ) ≠ 0 := ne_of_gt hqpos
  have hsep := PiIrrationality.remainder_separation
    ((((Real.pi - (p : ℝ) / (q : ℝ)) / 2 : ℝ) : ℂ) * Complex.I)
    0 R U T (1 / (32 * (q : ℝ)^5)) ((q : ℝ)^15 / 32)
    (by simpa using hid) (by positivity) (by positivity) hU hR hT
  have hnorm : ‖(((Real.pi - (p : ℝ) / (q : ℝ)) / 2 : ℝ) : ℂ) * Complex.I - 0‖ =
      |Real.pi - (p : ℝ) / (q : ℝ)| / 2 := by
    simp only [sub_zero, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [hnorm] at hsep
  have hfrac : (1 / (32 * (q : ℝ)^5)) / (2 * ((q : ℝ)^15 / 32)) =
      (1 / (q : ℝ)^20) / 2 := by
    field_simp
  rw [hfrac] at hsep
  linarith

theorem solution : PiIrrationality.UpperBound (20.6 : ℝ) := by
  apply PiIrrationality.UpperBound.mono (B := (20.6 : ℝ)) (A := 20) _ (by norm_num)
  apply PiIrrationality.upperBound_twenty_of_eventual_near_power_bound
  obtain ⟨Q, hQ⟩ := PiIrrationality.mignotte_parameter_selection
  refine ⟨Q, ?_⟩
  intro p q hp hq hQq hnear
  obtain ⟨n, hn, hRbound, hTbound⟩ := hQ q hq hQq
  obtain ⟨R, U, T, hid, hU, hR, hT⟩ :=
    PiIrrationality.mignotte_hermite_estimates n hn p q hp hq hnear
  have hcert := mignotte_certificate_bridge p q hq
    ⟨R, U, T, hid, hU, hR.trans hRbound, lt_of_le_of_lt hT hTbound⟩
  simpa only [show (20 : ℝ) = ((20 : ℕ) : ℝ) from rfl, Real.rpow_natCast] using hcert.le
