-- Prove2me | solution 1 for P2M_FixedOrderFactor_sqrtCount_imaginary__18e778af86a9
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:04:31.488332+00:00
-- url     : https://prove2.me/submissions/2b8d6027-c365-43a6-9fea-fda2f682f1f0

module
public import Definitions.Def_FixedOrderFactor_Local
public import Definitions.Def_FixedOrderFactor_Bias
public import Theorems.Thm_FixedOrderFactor_not_pow_succ_dvd_sq_sub_one

set_option autoImplicit true
@[expose] public section
public section
open Finset Real Complex
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution {r : ℕ} (hr : 0 < r) (hev : Even r) :
    (¬ 8 ∣ r → ∀ s, sqrtCount (2 * r) (1 + r) s = 0) ∧
      (∀ d, d ∣ r → ¬ 2 ∣ d → sqrtCount (2 * r) (1 + r) (r / d) = 0) := by
  set k := r.factorization 2 with hkdef
  have hk1 : 0 < k := Nat.prime_two.factorization_pos_of_dvd hr.ne' (even_iff_two_dvd.1 hev)
  -- an element of the count is odd
  have hodd : ∀ x, Nat.Coprime x (2 * r) → Odd x := by
    intro x hx
    exact Nat.coprime_two_right.1 (Nat.Coprime.coprime_dvd_right (dvd_mul_right 2 r) hx)
  constructor
  · intro h8 s
    rw [sqrtCount, card_eq_zero, filter_eq_empty_iff]
    rintro x - ⟨hcop, hsq, -⟩
    obtain ⟨m, rfl⟩ := hodd x hcop
    have hk3 : k + 1 ≤ 3 := by
      by_contra hc
      apply h8
      exact (pow_dvd_pow 2 (by omega : 3 ≤ k)).trans (Nat.ordProj_dvd r 2)
    apply not_pow_succ_dvd_sq_sub_one hr hsq
    have h8x : (8 : ℤ) ∣ ((2 * m + 1 : ℕ) : ℤ) ^ 2 - 1 := by
      obtain ⟨j, hj⟩ := Int.even_mul_succ_self (m : ℤ)
      refine ⟨j, ?_⟩
      push_cast
      linear_combination 4 * hj
    refine dvd_trans ?_ h8x
    have : 2 ^ (k + 1) ∣ 8 := (pow_dvd_pow 2 hk3)
    exact_mod_cast this
  · intro d hd hdodd
    rw [sqrtCount, card_eq_zero, filter_eq_empty_iff]
    rintro x - ⟨-, hsq, hs⟩
    -- `2^k ∣ r/d` since `d` is odd
    have hks : 2 ^ k ∣ r / d := by
      have hrd : r = d * (r / d) := (Nat.mul_div_cancel' hd).symm
      have hcop : Nat.Coprime (2 ^ k) d :=
        Nat.Coprime.pow_left k ((Nat.prime_two.coprime_iff_not_dvd).2 hdodd)
      exact hcop.dvd_of_dvd_mul_left (hrd ▸ Nat.ordProj_dvd r 2)
    obtain ⟨y, hy⟩ := hks.trans hs
    apply not_pow_succ_dvd_sq_sub_one hr hsq
    obtain ⟨j, hj⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    refine ⟨(y : ℤ) * (2 ^ j * y - 1), ?_⟩
    have hxy : (x : ℤ) = 2 ^ k * y - 1 := by
      have : ((x + 1 : ℕ) : ℤ) = ((2 ^ k * y : ℕ) : ℤ) := by rw [hy]
      push_cast at this; linarith
    rw [hxy, ← hkdef, hj]
    push_cast
    ring
end FixedOrderFactor
