-- Prove2me | solution 1 for SmallRatio.sum_floor_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:21:49.612953+00:00
-- url     : https://prove2.me/submissions/12aee2f0-2787-45a2-af0f-84d7aeb70afa

module
public import Definitions.Def_SmallRatio_Defs
public import Definitions.Def_SmallRatio_Reciprocity
public import Theorems.Thm_SmallRatio_sum_odd

set_option autoImplicit true
@[expose] public section
public section
open SmallRatio
open Finset
namespace SmallRatio
theorem _root_.solution (h k : ℕ) (hh : 0 < h) (hk : 0 < k) (hc : Nat.Coprime h k) :
    ∑ r ∈ range k, ((h * r / k : ℕ) : ℤ) ^ 2 =
      ∑ j ∈ Ico 1 h, (2 * (j : ℤ) - 1) * ((k : ℤ) - 1 - ((k * j / h : ℕ) : ℤ)) := by
  have hle : ∀ r ∈ range k, h * r / k < h := by
    intro r hr
    rw [mem_range] at hr
    rw [Nat.div_lt_iff_lt_mul hk]
    exact Nat.mul_lt_mul_of_pos_left hr hh
  have step1 : ∀ r ∈ range k, ((h * r / k : ℕ) : ℤ) ^ 2 =
      ∑ j ∈ Ico 1 h, if j ≤ h * r / k then (2 * (j : ℤ) - 1) else 0 := by
    intro r hr
    rw [← sum_odd, sum_ite, sum_const_zero, add_zero]
    congr 1
    ext j
    simp only [mem_Ico, mem_filter]
    have := hle r hr
    omega
  rw [sum_congr rfl step1, sum_comm]
  apply sum_congr rfl
  intro j hj
  rw [mem_Ico] at hj
  rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
  congr 1
  -- count the `r < k` with `j ≤ ⌊hr/k⌋`
  have hset : (range k).filter (fun r => j ≤ h * r / k) = Ioo (k * j / h) k := by
    ext r
    simp only [mem_filter, mem_range, mem_Ioo]
    rw [Nat.le_div_iff_mul_le hk, Nat.div_lt_iff_lt_mul hh]
    constructor
    · rintro ⟨hr, hjr⟩
      refine ⟨?_, hr⟩
      rcases Nat.lt_or_eq_of_le hjr with hlt | heq
      · linarith
      · exfalso
        have : h ∣ k * j := ⟨r, by linarith⟩
        have := Nat.le_of_dvd (by omega) ((Nat.Coprime.dvd_of_dvd_mul_left hc) this)
        omega
    · rintro ⟨hjr, hr⟩
      exact ⟨hr, by linarith⟩
  rw [hset, Nat.card_Ioo]
  have hlt : k * j / h < k := by
    rw [Nat.div_lt_iff_lt_mul hh]
    exact Nat.mul_lt_mul_of_pos_left hj.2 hk
  generalize k * j / h = g at hlt ⊢
  omega
end SmallRatio
