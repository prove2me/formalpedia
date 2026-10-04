-- Prove2me | solution 1 for OddPerfectNumber.q2_five_q3_nineteen_q4_127_five_dvd_sigma
-- status  : ACCEPTED   (prove)
-- author  : @Patrick
-- created : 2026-09-18T02:07:44.803688+00:00
-- url     : https://prove2.me/submissions/62cb1aae-cb1c-4014-94bd-697f7a7a0cb1

import Mathlib.Data.Nat.Prime.Basic

theorem solution (p m d sigma : Nat)
    (hprod : m ^ 2 = ((p + 1) / 2) * d) (hsigma : sigma = p * d)
    (hD : (p + 1) / 2 < 185) (hpow : 5 ^ 6 ∣ m ^ 2) : 5 ∣ sigma := by
  rw [hsigma]
  by_cases hp0 : p = 0
  · simp [hp0]
  have hDpos : 0 < (p + 1) / 2 := by omega
  by_cases hd : 5 ∣ d
  · exact dvd_mul_of_dvd_right hd p
  have hcop : Nat.Coprime 5 d := (show Nat.Prime 5 by decide).coprime_iff_not_dvd.mpr hd
  have hpow' : 5 ^ 6 ∣ (p + 1) / 2 * d := by simpa only [hprod] using hpow
  have hDdiv : 5 ^ 6 ∣ (p + 1) / 2 := (hcop.pow_left 6).dvd_of_dvd_mul_right hpow'
  have hle := Nat.le_of_dvd hDpos hDdiv
  omega

/-- info: 'solution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms solution
