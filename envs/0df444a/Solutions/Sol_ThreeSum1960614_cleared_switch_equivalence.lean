-- Prove2me | solution 1 for ThreeSum1960614.cleared_switch_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-14T06:44:30.102665+00:00
-- url     : https://prove2.me/submissions/2c3fd5c1-739d-4a83-8b9a-74d7c5138590

-- Clearing positive denominators adapts the pinned upstream Switch.lean argument.
import Definitions.Def_ThreeSum1960614_Analysis

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
open ThreeSum1960614

private theorem threshold_fraction {J j : ℕ} (hJ : 0 < J) (hj : j < J) :
    threshold ((j : ℝ) / J) =
      (159243801 * (J : ℝ) + 500000000 * j) / (500000000 * ((J - j : ℕ) : ℝ)) := by
  have hJR : (J : ℝ) ≠ 0 := by exact_mod_cast hJ.ne'
  have hd : ((J - j : ℕ) : ℝ) = (J : ℝ) - j := Nat.cast_sub hj.le
  have hden : (J : ℝ) - j ≠ 0 := by
    have hlt : (j : ℝ) < J := by exact_mod_cast hj
    linarith
  rw [hd]
  unfold threshold v saving beta
  field_simp [hJR, hden]
  <;> ring

private theorem phi_fraction {r q : ℕ} (hr : 0 < r) :
    phi ((q : ℝ) / r) =
      ((785174904 * q * r ^ 3 + 72447023 * q ^ 2 * r ^ 2 +
        24044466 * q ^ 3 * r + 12022459 * q ^ 4 : ℕ) : ℝ) /
          (100000000 * (r : ℝ) ^ 4) := by
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  simp only [phi, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  field_simp [hrR]
  <;> ring

theorem solution (J s j q : ℕ) (hJ : 0 < J) (hs : 0 < s) (hj : j < J) :
    clearedSwitch J s j q ↔
      threshold ((j : ℝ) / J) ≤ phi ((q : ℝ) / ((J - j) * s)) := by
  have hr : 0 < (J - j) * s := Nat.mul_pos (Nat.sub_pos_of_lt hj) hs
  have hdR : (0 : ℝ) < ((J - j : ℕ) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt hj
  have hrR : (0 : ℝ) < (((J - j) * s : ℕ) : ℝ) := by exact_mod_cast hr
  have hcastR : ((J : ℝ) - j) * s = (((J - j) * s : ℕ) : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_sub hj.le]
  rw [hcastR]
  rw [threshold_fraction hJ hj, phi_fraction hr,
    div_le_div_iff₀ (by positivity) (by positivity)]
  have hc : clearedSwitch J s j q ↔
      100000000 * (159243801 * (J : ℝ) + 500000000 * j) *
          ((((J - j) * s : ℕ) : ℝ) ^ 4) ≤
        500000000 * ((J - j : ℕ) : ℝ) *
          ((785174904 * q * ((J - j) * s) ^ 3 +
            72447023 * q ^ 2 * ((J - j) * s) ^ 2 +
            24044466 * q ^ 3 * ((J - j) * s) + 12022459 * q ^ 4 : ℕ) : ℝ) := by
    unfold clearedSwitch
    exact_mod_cast Iff.rfl
  rw [hc]
  constructor <;> intro h <;> nlinarith only [h]

#print axioms solution
