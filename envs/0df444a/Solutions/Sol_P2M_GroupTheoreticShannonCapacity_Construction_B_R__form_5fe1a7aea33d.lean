-- Prove2me | solution 1 for P2M_GroupTheoreticShannonCapacity_Construction_B_R__form_5fe1a7aea33d
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:51:00.39312+00:00
-- url     : https://prove2.me/submissions/6505a943-d414-4e20-a664-aade70b0b232

import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_MAlpha
import Definitions.Def_GroupTheoreticShannonCapacity_Construction
import Theorems.Thm_P2M_GroupTheoreticShannonCapacity_Construction_B_R__form_nat_e28fa09a307e

set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.Construction
open Matrix
namespace GroupTheoreticShannonCapacity.Construction
theorem _root_.solution (n : ℕ) (k b r s : ℤ) (hn : 1 ≤ n) (hd : r + k * b ^ n ≠ 0)
    (hk : 1 ≤ k) (hb_pos : 1 ≤ b) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    let α := (r : ℚ) / (k : ℚ)
    let R := MAlpha.Rα n (α : ℝ)
    (matrixB n k b r s).map (↑· : ℚ → ℝ) =
    ((s : ℝ) • R - (a n k b r s : ℝ) • 1) *
    (R - (b : ℝ) • 1)⁻¹ := by
  intro α R
  -- Convert to natural number parameters
  obtain ⟨k', hk_eq⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ k)
  obtain ⟨b', hb_eq⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ b)
  obtain ⟨r', hr_eq⟩ := Int.eq_ofNat_of_zero_le hr
  obtain ⟨s', hs_eq⟩ := Int.eq_ofNat_of_zero_le hs
  have hk' : 1 ≤ k' := by omega
  have hb' : 1 ≤ b' := by omega
  -- The hypothesis hd in terms of naturals
  have hd' : (r' : ℤ) + (k' : ℤ) * (b' : ℤ) ^ n ≠ 0 := by
    simp only [hk_eq, hb_eq, hr_eq] at hd
    exact hd
  have h := B_Rα_form_nat n k' b' r' s' hn hk' hb' hd'
  simp only [hk_eq, hb_eq, hr_eq, hs_eq] at h ⊢
  have hR_eq : MAlpha.Rα n ((r' : ℝ) / (k' : ℝ)) = R := by
    congr 1
    simp only [α, Rat.cast_div, Rat.cast_intCast, hk_eq, hr_eq]
    simp only [Int.cast_natCast]
  rw [← hR_eq]
  exact h
end GroupTheoreticShannonCapacity.Construction
