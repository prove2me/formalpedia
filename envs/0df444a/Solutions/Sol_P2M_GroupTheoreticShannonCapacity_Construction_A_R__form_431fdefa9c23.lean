-- Prove2me | solution 1 for P2M_GroupTheoreticShannonCapacity_Construction_A_R__form_431fdefa9c23
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:51:03.519567+00:00
-- url     : https://prove2.me/submissions/fd559228-b6e3-4590-9b17-4926644a7337

import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_MAlpha
import Definitions.Def_GroupTheoreticShannonCapacity_Construction
import Theorems.Thm_P2M_GroupTheoreticShannonCapacity_Construction_A_R__form_nat_ec43854432ec

set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.Construction
open Matrix
namespace GroupTheoreticShannonCapacity.Construction
theorem _root_.solution (n : ℕ) (k b r s : ℤ) (hn : 1 ≤ n)
    (hk : 1 ≤ k) (hb : 1 ≤ b) (hs_pos : 1 ≤ s) (hr : 0 ≤ r)
    (hn_num : s ^ n * r + k * (a n k b r s) ^ n ≠ 0) :
    let α := (r : ℚ) / (k : ℚ)
    let R := MAlpha.Rα n (α : ℝ)
    (matrixA n k b r s).map (↑· : ℚ → ℝ) =
    ((p n k b r s : ℝ) • R - (p n k b r s * b : ℝ) • 1) *
    ((s : ℝ) • R - (a n k b r s : ℝ) • 1)⁻¹ := by
  intro α R
  -- Convert to natural number parameters
  obtain ⟨k', hk_eq⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ k)
  obtain ⟨b', hb_eq⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ b)
  obtain ⟨r', hr_eq⟩ := Int.eq_ofNat_of_zero_le hr
  obtain ⟨s', hs_eq⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ s)
  have hk' : 1 ≤ k' := by omega
  have hb' : 1 ≤ b' := by omega
  have hs' : 1 ≤ s' := by omega
  -- The hypothesis hn_num in terms of naturals
  have hn_num' :
      (s' : ℤ) ^ n * (r' : ℤ) + (k' : ℤ) * (a n (k':ℤ) (b':ℤ) (r':ℤ) (s':ℤ)) ^ n ≠ 0 := by
    simp only [hk_eq, hb_eq, hr_eq, hs_eq] at hn_num
    exact hn_num
  have h := A_Rα_form_nat n k' b' r' s' hn hk' hb' hs' hn_num'
  -- Convert the result: need to show MAlpha.Rα n (↑r' / ↑k') = R
  -- where R = MAlpha.Rα n (α : ℝ) and α = (r : ℚ) / (k : ℚ)
  simp only [hk_eq, hb_eq, hr_eq, hs_eq] at h ⊢
  -- The R in A_Rα_form_nat uses (↑r' / ↑k' : ℝ) directly from naturals
  -- Our R uses (α : ℝ) = ((r : ℚ) / (k : ℚ) : ℝ)
  -- These are equal when k = k' and r = r'
  have hR_eq : MAlpha.Rα n ((r' : ℝ) / (k' : ℝ)) = R := by
    congr 1
    simp only [α, Rat.cast_div, Rat.cast_intCast, hk_eq, hr_eq]
    simp only [Int.cast_natCast]
  rw [← hR_eq]
  exact h
end GroupTheoreticShannonCapacity.Construction
