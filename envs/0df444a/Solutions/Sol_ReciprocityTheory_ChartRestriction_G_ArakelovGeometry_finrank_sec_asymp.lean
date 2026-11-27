-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.finrank_sec_asymp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:24:45.599296+00:00
-- url     : https://prove2.me/submissions/af20d8f0-73f7-41ba-87dd-26f9b78668d5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_SectionModuleEqSpanPow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_EqZeroOfSecTraceMulEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ExistsNatMulMemConeRingIntFin
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ChooseLePowDivFactorial
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_le_finrank_sec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_finrank_sec_le
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_shift_pow_sub_pow_isBigO
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_pow_div_factorial_le_choose
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_choose_le_pow_div_factorial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo Module Filter Asymptotics
variable {Ω : Type*} [Field Ω] [CharZero Ω] {κ : Type*} [Fintype κ] {D : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution (x : κ → Ω) (e : Fin (D + 1) → κ) (h : IsProjFrame x e) :
    (fun n : ℕ => (finrank ℤ (sec ℤ x n) : ℝ) - (projDeg x e : ℝ) * (n : ℝ) ^ D / (D.factorial : ℝ))
      =O[atTop] fun n : ℕ => (n : ℝ) ^ D / (n : ℝ) := by
  obtain ⟨k1, hk1⟩ := le_finrank_sec x e h
  obtain ⟨k2, hk2⟩ := finrank_sec_le x e h
  have hup := (shift_pow_sub_pow_isBigO D ((k2 : ℝ) + D)).const_mul_left
    ((projDeg x e : ℝ) / D.factorial)
  have hlo := (shift_pow_sub_pow_isBigO D (-(k1 : ℝ))).const_mul_left
    ((projDeg x e : ℝ) / D.factorial)
  refine Asymptotics.IsBigO.trans ?_ (hup.norm_left.add hlo.norm_left)
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [Filter.eventually_ge_atTop k1] with n hn
  have hL : (projDeg x e : ℝ) * (((n - k1 : ℕ) : ℝ) ^ D / D.factorial) ≤ finrank ℤ (sec ℤ x n) := by
    have h1 := hk1 (n - k1)
    rw [Nat.sub_add_cancel hn] at h1
    have h1' : ((projDeg x e * (n - k1 + D).choose D : ℕ) : ℝ) ≤ (finrank ℤ (sec ℤ x n) : ℝ) := by
      exact_mod_cast h1
    push_cast at h1'
    exact le_trans (mul_le_mul_of_nonneg_left (pow_div_factorial_le_choose (n - k1) D) (Nat.cast_nonneg _)) h1'
  have hU : (finrank ℤ (sec ℤ x n) : ℝ) ≤ (projDeg x e : ℝ) * (((n + k2 + D : ℕ) : ℝ) ^ D / D.factorial) := by
    have h1 : ((finrank ℤ (sec ℤ x n) : ℕ) : ℝ) ≤ ((projDeg x e * (n + k2 + D).choose D : ℕ) : ℝ) := by
      exact_mod_cast hk2 n
    push_cast at h1
    exact le_trans h1 (mul_le_mul_of_nonneg_left (choose_le_pow_div_factorial (n + k2 + D) D) (Nat.cast_nonneg _))
  rw [Nat.cast_sub hn] at hL
  push_cast at hU
  rw [one_mul, Real.norm_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
  simp only [Real.norm_eq_abs]
  have eA : (projDeg x e : ℝ) / D.factorial * (((n : ℝ) + ((k2 : ℝ) + D)) ^ D - (n : ℝ) ^ D) =
      (projDeg x e : ℝ) * (((n : ℝ) + k2 + D) ^ D / D.factorial) - (projDeg x e : ℝ) * (n : ℝ) ^ D / D.factorial := by
    ring
  have eB : (projDeg x e : ℝ) / D.factorial * (((n : ℝ) + -(k1 : ℝ)) ^ D - (n : ℝ) ^ D) =
      (projDeg x e : ℝ) * (((n : ℝ) - k1) ^ D / D.factorial) - (projDeg x e : ℝ) * (n : ℝ) ^ D / D.factorial := by
    ring
  have a1 := le_abs_self ((projDeg x e : ℝ) / D.factorial * (((n : ℝ) + ((k2 : ℝ) + D)) ^ D - (n : ℝ) ^ D))
  have a2 := neg_abs_le ((projDeg x e : ℝ) / D.factorial * (((n : ℝ) + -(k1 : ℝ)) ^ D - (n : ℝ) ^ D))
  have a3 := abs_nonneg ((projDeg x e : ℝ) / D.factorial * (((n : ℝ) + ((k2 : ℝ) + D)) ^ D - (n : ℝ) ^ D))
  have a4 := abs_nonneg ((projDeg x e : ℝ) / D.factorial * (((n : ℝ) + -(k1 : ℝ)) ^ D - (n : ℝ) ^ D))
  rw [abs_le]
  constructor <;> linarith
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
