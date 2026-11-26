-- Prove2me | solution 1 for P2M_FixedOrderFactor_hasProd_correctionFactor__ac45d6c11465
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:59:40.825721+00:00
-- url     : https://prove2.me/submissions/8604f425-73f0-41b5-bf91-1e8c5f700f3b

module
public import Definitions.Def_FixedOrderFactor_Defs
public import Definitions.Def_FixedOrderFactor_Euler
public import Theorems.Thm_FixedOrderFactor_hasProd_zetaN
public import Theorems.Thm_FixedOrderFactor_zetaN_pos
public import Theorems.Thm_FixedOrderFactor_pow_inv_q_lt_one

set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution (N : Finset Nat.Primes) {r : ℕ} (hr : 2 ≤ r) :
    HasProd (fun q : {q : Nat.Primes // q ∉ N} =>
        (1 + (1 / (q : ℝ)) ^ r) / (1 - (1 / (q : ℝ)) ^ r))
      (correctionFactor N r) := by
  have hA := hasProd_zetaN N hr
  have hB := (hasProd_zetaN N (by omega : 2 ≤ 2 * r)).inv₀ (zetaN_pos N (by omega)).ne'
  have := (hA.mul hA).mul hB
  unfold correctionFactor
  convert this using 1
  · funext q
    have h1 : 1 - (1 / ((q : Nat.Primes) : ℝ)) ^ r ≠ 0 :=
      sub_ne_zero.mpr (pow_inv_q_lt_one q.1 (by omega)).ne'
    simp only [inv_inv, pow_mul]
    field_simp
    ring
  · rw [div_eq_mul_inv, sq]
end FixedOrderFactor
