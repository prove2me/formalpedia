-- Prove2me | solution 1 for SZ.sqrt_mem_MahlerZ_of_four_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:04:39.159947+00:00
-- url     : https://prove2.me/submissions/3ff08487-90e2-4a59-8596-d83e62cad543

import Definitions.Def_SZ_SliceHygiene
import Mathlib.Tactic.Push
import Mathlib.Tactic.IntervalCases
import Definitions.Def_SZ_ThmC
import Theorems.Thm_SZ_exists_dvd_floor_sqrt

set_option autoImplicit false
open SZ
namespace SZ
theorem _root_.solution {m : ℕ} (hm : 4 ≤ m) (hns : ¬ IsSquare m) :
    Real.sqrt m ∈ MahlerZ := by
  have hm5 : 5 ≤ m := by
    rcases Nat.lt_or_ge m 5 with h | h
    · interval_cases m
      exact absurd ⟨2, by norm_num⟩ hns
    · exact h
  have hcase : ((2 : ℤ) ∣ (m : ℤ) - 1 ∧ (2 : ℤ) ^ 2 ≤ (m : ℤ)) ∨
      ((2 : ℤ) ∣ (m : ℤ) ∧
        ((2 : ℤ) : ℝ) * ((m : ℝ) - 1) < ((m : ℝ) - ((2 : ℤ) : ℝ)) * (1 + Real.sqrt m)) := by
    rcases Nat.even_or_odd m with he | ho
    · refine Or.inr ⟨?_, ?_⟩
      · obtain ⟨k, hk⟩ := he
        exact ⟨(k : ℤ), by push_cast [hk]; ring⟩
      · have hs := p_lt_sqrt (p := 2) (m := m) (by norm_num)
          (by exact_mod_cast (by omega : 4 < m))
        have hs2 : Real.sqrt (m : ℝ) ^ 2 = (m : ℝ) := Real.sq_sqrt (by positivity)
        have hs0 : (0 : ℝ) ≤ Real.sqrt m := Real.sqrt_nonneg _
        push_cast at hs ⊢
        nlinarith [mul_pos (mul_pos (by linarith : (0:ℝ) < Real.sqrt m)
          (by linarith : (0:ℝ) < Real.sqrt m - 2)) (by linarith : (0:ℝ) < Real.sqrt m + 1)]
    · refine Or.inl ⟨?_, by exact_mod_cast (by omega : 4 ≤ m)⟩
      obtain ⟨k, hk⟩ := ho
      exact ⟨(k : ℤ), by push_cast [hk]; ring⟩
  obtain ⟨ξ, hξ, hdvd⟩ := exists_dvd_floor_sqrt 2 m (by norm_num) (by omega) hns hcase
  refine ⟨?_, ξ, ne_of_gt hξ, fun n hn => even_iff_two_dvd.mpr (hdvd n hn)⟩
  have h : Real.sqrt 1 < Real.sqrt m :=
    Real.sqrt_lt_sqrt (by norm_num) (by exact_mod_cast (by omega : 1 < m))
  rwa [Real.sqrt_one] at h
end SZ
