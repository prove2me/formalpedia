-- Prove2me | solution 1 for P2M_FixedOrderFactor_correctionFactor_even__20a8b73c46be
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:58:12.701369+00:00
-- url     : https://prove2.me/submissions/9b696b17-e4bb-4e46-95a7-bdbdeeda918a

module
public import Definitions.Def_FixedOrderFactor_Order
public import Definitions.Def_FixedOrderFactor_Values
public import Theorems.Thm_FixedOrderFactor_zetaN_empty_two_mul
public import Theorems.Thm_FixedOrderFactor_zetaN_pos


set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology Finset
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution {k : ℕ} (hk : 0 < k) :
    correctionFactor ∅ (2 * k) =
      -((Nat.choose (4 * k) (2 * k) : ℝ) * (bernoulli (2 * k) : ℝ) ^ 2 /
        (2 * (bernoulli (4 * k) : ℝ))) := by
  have hZ := zetaN_pos ∅ (by omega : 2 ≤ 2 * (2 * k))
  unfold correctionFactor
  rw [show 2 * (2 * k) = 2 * (2 * k) from rfl] at hZ ⊢
  rw [zetaN_empty_two_mul hk.ne', zetaN_empty_two_mul (by omega : 2 * k ≠ 0)] at *
  rw [show 2 * (2 * k) = 4 * k by ring] at *
  have hB : (bernoulli (4 * k) : ℝ) ≠ 0 := by
    intro h; rw [h] at hZ; simp at hZ
  have hch : ((4 * k).factorial : ℝ) =
      (Nat.choose (4 * k) (2 * k) : ℝ) * (2 * k).factorial * (2 * k).factorial := by
    have := Nat.choose_mul_factorial_mul_factorial (by omega : 2 * k ≤ 4 * k)
    rw [show 4 * k - 2 * k = 2 * k by omega] at this
    exact_mod_cast this.symm
  have h2 : (2 : ℝ) ^ (4 * k - 1) = 2 * ((2 : ℝ) ^ (2 * k - 1)) ^ 2 := by
    rw [← pow_mul, ← pow_succ']; congr 1; omega
  have hm1 : ((-1 : ℝ) ^ (2 * k + 1)) = -1 := by
    rw [pow_succ, pow_mul]; norm_num
  have hm2 : ((-1 : ℝ) ^ (k + 1)) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hpi : (π ^ (2 * k)) ^ 2 = π ^ (4 * k) := by rw [← pow_mul]; ring_nf
  rw [hch, h2, hm1, div_pow, mul_pow, mul_pow, mul_pow, hm2, hpi]
  have hf : ((2 * k).factorial : ℝ) ≠ 0 := by positivity
  have hp : π ^ (4 * k) ≠ 0 := by positivity
  have h2' : ((2 : ℝ) ^ (2 * k - 1)) ≠ 0 := by positivity
  field_simp
end FixedOrderFactor
