-- Prove2me | solution 1 for OddPerfectNumber.Kernel.five_m_is_three_times_four_factor_form
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T15:19:29.427317+00:00
-- url     : https://prove2.me/submissions/803dc7ea-ff8f-4df5-87a6-c52fe146afd9

import Mathlib

namespace P2M6f5c2175

theorem sq_of_cop (x y c : Nat) (hc : Nat.Coprime x y) (h : x * y = c ^ 2) : ∃ d, x = d ^ 2 := by
  have hu : IsUnit (gcd x y) := by
    rw [Nat.isUnit_iff]; exact hc
  exact exists_eq_pow_of_mul_eq_pow hu h

end P2M6f5c2175

theorem solution (p m d1 q r u a b : Nat)
    (hp : Nat.Prime p) (hp4 : p % 4 = 1) (hd1 : d1 != 0)
    (he : (p + 1) / 6 = u ^ 2)
    (hc : p ^ 2 + p + 1 = q * a ^ 2)
    (hf : (p ^ 2 - p + 1) / 3 = r * b ^ 2)
    (h1 : 2 * m ^ 2 = (2 * (p ^ 2 + p + 1) * ((p + 1) / 2 * (p ^ 2 - p + 1))) *
      (d1 ^ 2 * (q * r))) :
    m = 3 * u * a * b * d1 * q * r := by
  have hp2 : 2 ≤ p := hp.two_le
  obtain ⟨D, hDdef⟩ : ∃ D, D = p ^ 2 - p + 1 := ⟨_, rfl⟩
  have hpp : p ≤ p ^ 2 := by nlinarith
  have hDz : (D : Int) = (p : Int) ^ 2 - p + 1 := by
    rw [hDdef]; push_cast [Nat.sub_add_comm hpp, hpp]; ring
  rw [← hDdef] at h1 hf
  have hm2 : m ^ 2 = q * a ^ 2 * ((p + 1) / 2 * D) * (d1 ^ 2 * (q * r)) := by
    rw [← hc]; linarith
  have h3 : p % 3 = 1 ∨ p % 3 = 2 := by
    have : p % 3 ≠ 0 := by
      intro h0
      have h3d : 3 ∣ p := Nat.dvd_of_mod_eq_zero h0
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h3d
      omega
    omega
  rcases h3 with h3 | h3
  · -- impossible unless r = 0
    rcases Nat.eq_zero_or_pos r with hr | hr
    · subst hr
      have : m ^ 2 = 0 := by rw [hm2]; ring
      have : m = 0 := by simpa using this
      subst this; ring
    exfalso
    obtain ⟨k, hk⟩ : ∃ k, p = 3 * k + 1 := ⟨p / 3, by omega⟩
    have hDk : D = 3 * (3 * k ^ 2 + k) + 1 := by
      have : (D : Int) = 3 * (3 * k ^ 2 + k) + 1 := by rw [hDz, hk]; push_cast; ring
      exact_mod_cast this
    have hrb : r * b ^ 2 = 3 * k ^ 2 + k := by
      rw [← hf, hDk]; omega
    have hD3 : D = 3 * (r * b ^ 2) + 1 := by rw [hrb]; exact hDk
    -- B = (p+1)/2
    obtain ⟨B, hB⟩ : ∃ B, B = (p + 1) / 2 := ⟨_, rfl⟩
    have hB2 : p + 1 = 2 * B := by omega
    rw [← hB] at hm2
    -- coprime D (B * r)
    have hcop : Nat.Coprime D (B * r) := by
      apply Nat.Coprime.mul_right
      · -- gcd D B divides 3 and 3 ∤ D
        have hDB : (D : Int) = (2 * B) * ((2 * B) - 3) + 3 := by
          rw [hDz]; have : (p : Int) = 2 * B - 1 := by omega
          rw [this]; ring
        rw [Nat.coprime_comm, Nat.Coprime]
        set g := Nat.gcd B D with hg
        have hgB : g ∣ B := Nat.gcd_dvd_left B D
        have hgD : g ∣ D := Nat.gcd_dvd_right B D
        have hg3 : (g : Int) ∣ 3 := by
          have h1' : (g : Int) ∣ D := by exact_mod_cast hgD
          have h2' : (g : Int) ∣ (2 * B) * ((2 * B) - 3) := by
            apply Dvd.dvd.mul_right; apply Dvd.dvd.mul_left; exact_mod_cast hgB
          have := dvd_sub h1' h2'
          rw [hDB] at this; simpa using this
        have hg3' : g ∣ 3 := by exact_mod_cast hg3
        have : g = 1 ∨ g = 3 := by
          have := (Nat.dvd_prime Nat.prime_three).mp hg3'; exact this
        rcases this with h | h
        · exact h
        · exfalso; rw [h] at hgD; omega
      · rw [Nat.Coprime]
        have : Nat.gcd D r ∣ 1 := by
          have h1' : Nat.gcd D r ∣ D := Nat.gcd_dvd_left D r
          have h2' : Nat.gcd D r ∣ 3 * (r * b ^ 2) := by
            apply Dvd.dvd.mul_left; apply Dvd.dvd.mul_right; exact Nat.gcd_dvd_right D r
          have h1'' : Nat.gcd D r ∣ 3 * (r * b ^ 2) + 1 := by rw [← hD3]; exact h1'
          exact (Nat.dvd_add_right h2').mp h1''
        exact Nat.dvd_one.mp this
    -- B * D * r is a square
    have hqa : 0 < q * a * d1 := by
      have : 0 < q * a ^ 2 := by rw [← hc]; positivity
      have hq : 0 < q := Nat.pos_of_mul_pos_right this
      have ha : 0 < a := by
        rcases Nat.eq_zero_or_pos a with h | h
        · subst h; simp at this
        · exact h
      have : 0 < d1 := by
        rcases Nat.eq_zero_or_pos d1 with h | h
        · subst h; simp at hd1
        · exact h
      positivity
    have hsq : (q * a * d1) ^ 2 * (D * (B * r)) = m ^ 2 := by rw [hm2]; ring
    have hdvd : q * a * d1 ∣ m := by
      have : (q * a * d1) ^ 2 ∣ m ^ 2 := ⟨_, hsq.symm⟩
      exact (Nat.pow_dvd_pow_iff (by norm_num)).mp this
    obtain ⟨c, hcm⟩ := hdvd
    have hX : D * (B * r) = c ^ 2 := by
      rw [hcm] at hsq
      have hpos : 0 < (q * a * d1) ^ 2 := by positivity
      have : (q * a * d1) ^ 2 * (D * (B * r)) = (q * a * d1) ^ 2 * c ^ 2 := by rw [hsq]; ring
      exact Nat.eq_of_mul_eq_mul_left hpos this
    obtain ⟨e, he'⟩ := P2M6f5c2175.sq_of_cop D (B * r) c hcop hX
    have hE : (e : Int) ^ 2 = (p : Int) ^ 2 - p + 1 := by
      rw [← hDz]; exact_mod_cast he'.symm
    have hp1 : (2 : Int) ≤ p := by exact_mod_cast hp2
    have h0 : (0 : Int) ≤ e := by positivity
    rcases le_or_gt (e : Int) ((p : Int) - 1) with h | h
    · have hm : (e : Int) * e ≤ ((p : Int) - 1) * ((p : Int) - 1) :=
        mul_le_mul h h h0 (by linarith)
      have : (e : Int) ^ 2 = (e : Int) * e := by ring
      linarith
    · have hpe : (p : Int) ≤ e := by omega
      have hm : (p : Int) * p ≤ (e : Int) * e :=
        mul_le_mul hpe hpe (by linarith) h0
      have : (e : Int) ^ 2 = (e : Int) * e := by ring
      have : (p : Int) ^ 2 = (p : Int) * p := by ring
      linarith
  · -- p % 3 = 2: p % 6 = 5
    have hp6 : (p + 1) % 6 = 0 := by omega
    have hpu : p + 1 = 6 * u ^ 2 := by rw [← he]; omega
    have hB : (p + 1) / 2 = 3 * u ^ 2 := by omega
    obtain ⟨k, hk⟩ : ∃ k, p = 3 * k + 2 := ⟨p / 3, by omega⟩
    have hDk : D = 3 * (3 * k ^ 2 + 3 * k + 1) := by
      have : (D : Int) = 3 * (3 * k ^ 2 + 3 * k + 1) := by rw [hDz, hk]; push_cast; ring
      exact_mod_cast this
    have hD : D = 3 * (r * b ^ 2) := by rw [← hf, hDk]; omega
    rw [hB, hD] at hm2
    have : m ^ 2 = (3 * u * a * b * d1 * q * r) ^ 2 := by rw [hm2]; ring
    exact (Nat.pow_left_injective (by norm_num : (2:Nat) ≠ 0)) this
