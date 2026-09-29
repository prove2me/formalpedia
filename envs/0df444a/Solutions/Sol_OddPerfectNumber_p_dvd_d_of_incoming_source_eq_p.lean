-- Prove2me | solution 1 for OddPerfectNumber.p_dvd_d_of_incoming_source_eq_p
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-12T17:59:00.079345+00:00
-- url     : https://prove2.me/submissions/d2ca3d5d-af24-4846-a075-ac978214112a

import Mathlib

theorem solution (p m d r : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1)
    (hdvd : m ^ 2 = ((p + 1) / 2) * d)
    (hrmem : r ∈ (m ^ 2).primeFactors)
    (hrp : r = p) :
    p ∣ d := by
  subst r
  have hm2 : m ^ 2 ≠ 0 := by
    obtain ⟨_, _, hm2⟩ := Nat.mem_primeFactors.mp hrmem
    exact hm2
  have hpm2 : p ∣ m ^ 2 := Nat.dvd_of_mem_primeFactors hrmem
  have hp2 : p ≠ 2 := by
    intro h
    subst p
    norm_num at hp4
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hp1 : p + 1 = 2 * ((p + 1) / 2) := by
    obtain ⟨u, hu⟩ := hpodd
    omega
  have hpt : ¬ p ∣ (p + 1) / 2 := by
    intro h
    have hpdiv : p ∣ p + 1 := by
      rw [hp1]
      exact dvd_mul_of_dvd_right h 2
    have hpdiv1 : p ∣ 1 := by
      have := (Nat.dvd_add_iff_right (dvd_mul_right p 1)).mp hpdiv
      simpa using this
    exact hp.not_dvd_one hpdiv1
  have hprod : p ∣ ((p + 1) / 2) * d := by
    rw [← hdvd]
    exact hpm2
  rcases hp.dvd_mul.mp hprod with hpt' | hpd
  · exact False.elim (hpt hpt')
  · exact hpd
