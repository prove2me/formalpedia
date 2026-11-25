-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.TR.Weyl.tele_nat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:42:22.061039+00:00
-- url     : https://prove2.me/submissions/918b3210-bf0e-44dd-b6e5-640b00fcde4b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_SymplecticTraces_WeylCharacters_AltBranchStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_SymplecticTraces_WeylCharacters_AntitoneOfMemInterl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.TR ReciprocityTheory.ChartRestriction.TR.Weyl
namespace ReciprocityTheory.ChartRestriction.TR.Weyl
theorem _root_.solution {K : Type*} [Field K] {t y : K} (ht : t ≠ 0) (hy : y ≠ 0) (c e : ℤ) (k : ℕ) :
    (t - y) * ∑ m ∈ Icc c (c - 1 + k), t ^ (m + e) * y ^ (c - 1 + k - m) =
      t ^ (c - 1 + k + 1 + e) - y ^ (c - 1 + k - c + 1) * t ^ (c + e) := by
  induction k with
  | zero =>
    have h0 : Icc c (c - 1 + ((0 : ℕ) : ℤ)) = ∅ := Finset.Icc_eq_empty (by push_cast; omega)
    rw [h0, sum_empty, mul_zero]
    have h1 : c - 1 + ((0 : ℕ) : ℤ) + 1 + e = c + e := by push_cast; ring
    have h2 : c - 1 + ((0 : ℕ) : ℤ) - c + 1 = 0 := by push_cast; ring
    rw [h1, h2, zpow_zero, one_mul, sub_self]
  | succ k ih =>
    have hb' : c - 1 + ((k + 1 : ℕ) : ℤ) = (c - 1 + k) + 1 := by push_cast; ring
    rw [hb']
    have hk0 : (0 : ℤ) ≤ k := Int.natCast_nonneg k
    have hI : Icc c (c - 1 + (k : ℤ) + 1) = insert (c - 1 + (k : ℤ) + 1) (Icc c (c - 1 + k)) := by
      ext x; simp only [mem_insert, mem_Icc]; omega
    have hnot : c - 1 + (k : ℤ) + 1 ∉ Icc c (c - 1 + k) := by simp
    rw [hI, sum_insert hnot]
    have hz : c - 1 + (k : ℤ) + 1 - (c - 1 + (k : ℤ) + 1) = 0 := by ring
    rw [hz, zpow_zero, mul_one]
    have hs : ∑ m ∈ Icc c (c - 1 + (k : ℤ)), t ^ (m + e) * y ^ (c - 1 + (k : ℤ) + 1 - m) =
        y * ∑ m ∈ Icc c (c - 1 + (k : ℤ)), t ^ (m + e) * y ^ (c - 1 + (k : ℤ) - m) := by
      rw [mul_sum]; refine sum_congr rfl fun m _ => ?_
      rw [show c - 1 + (k : ℤ) + 1 - m = (c - 1 + (k : ℤ) - m) + 1 by ring, zpow_add_one₀ hy]; ring
    rw [hs, mul_add, mul_left_comm, ih]
    have e1 : t ^ (c - 1 + (k : ℤ) + 1 + 1 + e) = t ^ (c - 1 + (k : ℤ) + 1 + e) * t := by
      rw [← zpow_add_one₀ ht]; congr 1; ring
    have e2 : y ^ (c - 1 + (k : ℤ) + 1 - c + 1) = y ^ (c - 1 + (k : ℤ) - c + 1) * y := by
      rw [← zpow_add_one₀ hy]; congr 1; ring
    rw [e1, e2]
    generalize t ^ (c - 1 + (k : ℤ) + 1 + e) = A
    generalize y ^ (c - 1 + (k : ℤ) - c + 1) = Y
    generalize t ^ (c + e) = C
    ring
end ReciprocityTheory.ChartRestriction.TR.Weyl
