-- Prove2me | solution 1 for RevenueOrdered.Ratio.sum_ratio_le_one_add_log
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T11:57:54.946985+00:00
-- url     : https://prove2.me/submissions/c02f3641-0eb7-4dd7-8aa4-d323ac500680

import Mathlib

set_option autoImplicit false

theorem sum_ratio_aux_98c5accf (k : ℕ) (a : ℕ → ℝ)
    (ha1 : 0 < a 1) (hmono : StrictMonoOn a (Set.Icc 1 k)) :
    ∀ n, 1 ≤ n → n ≤ k →
      ∑ l ∈ Finset.Icc 2 n, (a l - a (l - 1)) / a l ≤ Real.log (a n / a 1) := by
  have hpos : ∀ m, 1 ≤ m → m ≤ k → 0 < a m := by
    intro m h1 h2
    have : a 1 ≤ a m := hmono.monotoneOn ⟨le_refl 1, le_trans h1 h2⟩ ⟨h1, h2⟩ h1
    linarith
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    intro _
    simp [div_self (ne_of_gt ha1)]
  | succ n hn ih =>
    intro hnk
    have hn' : n ≤ k := Nat.le_of_succ_le hnk
    have h1 := ih hn'
    have hpn : 0 < a n := hpos n hn hn'
    have hpn1 : 0 < a (n + 1) := hpos (n + 1) (by omega) hnk
    rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ n + 1)]
    have hx : 0 < a (n + 1) / a n := div_pos hpn1 hpn
    have hlog := Real.one_sub_inv_le_log_of_pos hx
    have hsplit : Real.log (a (n + 1) / a 1)
        = Real.log (a (n + 1) / a n) + Real.log (a n / a 1) := by
      rw [← Real.log_mul (ne_of_gt hx) (ne_of_gt (div_pos hpn ha1))]
      congr 1
      field_simp
    have hterm : (a (n + 1) - a (n + 1 - 1)) / a (n + 1) = 1 - (a (n + 1) / a n)⁻¹ := by
      simp only [Nat.add_sub_cancel, inv_div]
      field_simp
    rw [hterm, hsplit]
    linarith

theorem solution (k : ℕ) (hk : 1 ≤ k) (a : ℕ → ℝ) (ha0 : a 0 = 0)
    (ha1 : 0 < a 1) (hmono : StrictMonoOn a (Set.Icc 1 k)) :
    ∑ l ∈ Finset.Icc 1 k, (a l - a (l - 1)) / a l =
        1 + ∑ l ∈ Finset.Icc 2 k, (a l - a (l - 1)) / a l ∧
      ∑ l ∈ Finset.Icc 1 k, (a l - a (l - 1)) / a l ≤ 1 + Real.log (a k / a 1) := by
  have heq : ∑ l ∈ Finset.Icc 1 k, (a l - a (l - 1)) / a l =
      1 + ∑ l ∈ Finset.Icc 2 k, (a l - a (l - 1)) / a l := by
    rw [Finset.Icc_eq_cons_Ioc hk, Finset.sum_cons]
    have : Finset.Ioc 1 k = Finset.Icc 2 k := by
      ext x; simp [Finset.mem_Ioc, Finset.mem_Icc]; omega
    rw [this]
    congr 1
    simp [ha0, div_self (ne_of_gt ha1)]
  refine ⟨heq, ?_⟩
  rw [heq]
  have := sum_ratio_aux_98c5accf k a ha1 hmono k hk le_rfl
  linarith
