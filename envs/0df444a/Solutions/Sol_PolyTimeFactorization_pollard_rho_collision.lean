-- Prove2me | solution 1 for PolyTimeFactorization.pollard_rho_collision
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T21:07:58.454039+00:00
-- url     : https://prove2.me/submissions/4669aa12-ad29-4f46-999a-dff5a5bdee31

import Mathlib
namespace PolyTimeFactorization

theorem pollard_rho_collision (n p : ℕ) (x y : ℤ) (hp : p.Prime) (hpn : p ∣ n)
    (hlt : p < n) (hcol : (p : ℤ) ∣ x - y) (hncol : ¬ (n : ℤ) ∣ x - y) :
    1 < Int.gcd (x - y) (n : ℤ) ∧ Int.gcd (x - y) (n : ℤ) < n := by
  have hn0 : 0 < n := lt_of_le_of_lt (Nat.zero_le p) hlt
  have hpg : p ∣ Int.gcd (x - y) (n : ℤ) := by
    have h1 : (p : ℤ) ∣ (n : ℤ) := Int.natCast_dvd_natCast.mpr hpn
    have := Int.dvd_coe_gcd hcol h1
    exact Int.natCast_dvd_natCast.mp this
  have hgpos : 0 < Int.gcd (x - y) (n : ℤ) :=
    Int.gcd_pos_of_ne_zero_right _ (by exact_mod_cast hn0.ne')
  have hgn : Int.gcd (x - y) (n : ℤ) ∣ n := by
    have := Int.gcd_dvd_right (x - y) (n : ℤ)
    exact Int.natCast_dvd_natCast.mp (by simpa using this)
  refine ⟨lt_of_lt_of_le hp.one_lt (Nat.le_of_dvd hgpos hpg), ?_⟩
  rcases lt_or_eq_of_le (Nat.le_of_dvd hn0 hgn) with h | h
  · exact h
  · exfalso
    apply hncol
    have := Int.gcd_dvd_left (x - y) (n : ℤ)
    rw [h] at this
    exact this

end PolyTimeFactorization

theorem solution (n p : ℕ) (x y : ℤ) (hp : p.Prime) (hpn : p ∣ n)
    (hlt : p < n) (hcol : (p : ℤ) ∣ x - y) (hncol : ¬ (n : ℤ) ∣ x - y) :
    1 < Int.gcd (x - y) (n : ℤ) ∧ Int.gcd (x - y) (n : ℤ) < n :=
  PolyTimeFactorization.pollard_rho_collision n p x y hp hpn hlt hcol hncol
