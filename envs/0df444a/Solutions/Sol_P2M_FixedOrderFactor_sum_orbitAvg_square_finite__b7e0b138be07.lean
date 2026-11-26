-- Prove2me | solution 1 for P2M_FixedOrderFactor_sum_orbitAvg_square_finite__b7e0b138be07
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:07:09.789914+00:00
-- url     : https://prove2.me/submissions/53f637e0-7ffd-407e-971e-3f6c30317273

module
public import Definitions.Def_FixedOrderFactor_Local
public import Definitions.Def_FixedOrderFactor_Bias
public import Theorems.Thm_P2M_FixedOrderFactor_sum_orbitAvg_mul__4157f1f1226d

set_option autoImplicit true
@[expose] public section
public section
open Finset Real Complex
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution {s : ℕ} (hs : 0 < s) (M a : ℕ) :
    ∑ x ∈ (range M).filter (fun x => Nat.Coprime x M ∧ x ^ 2 % M = a % M),
      ∑ t ∈ range s, orbitAvg s ((x + 1) * t) = s * sqrtCount M a s := by
  simp_rw [sum_orbitAvg_mul' hs]
  rw [← sum_filter, sum_const, nsmul_eq_mul, filter_filter, mul_comm]
  simp only [sqrtCount, and_assoc]
end FixedOrderFactor
