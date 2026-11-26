-- Prove2me | solution 1 for P2M_FixedOrderFactor_hasProd_muAvg__1e4c6588144b
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:01:00.832786+00:00
-- url     : https://prove2.me/submissions/7680a9d0-c093-49c8-8d94-3f43cb093282

module
public import Definitions.Def_FixedOrderFactor_Euler
public import Definitions.Def_FixedOrderFactor_Local
public import Definitions.Def_FixedOrderFactor_Model
public import Theorems.Thm_FixedOrderFactor_abs_inv_q_lt_one
public import Theorems.Thm_FixedOrderFactor_hasProd_zetaN
public import Theorems.Thm_FixedOrderFactor_pow_inv_q_lt_one
public import Theorems.Thm_P2M_FixedOrderFactor_hasProd_correctionFactor__ac45d6c11465
public import Theorems.Thm_P2M_FixedOrderFactor_muAvg_eq__11fccbbf11a9


set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology Finset
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution (N : Finset Nat.Primes) {r : ℕ} (hr : 2 ≤ r) :
    HasProd (fun q : {q : Nat.Primes // q ∉ N} => muAvg r (1 / (q : ℝ)))
      (zetaN N 2 * correctionFactor N r) := by
  have := (hasProd_zetaN N le_rfl).mul (hasProd_correctionFactor' N hr)
  convert this using 1
  funext q
  rw [muAvg_eq' (by omega) (abs_inv_q_lt_one q.1)]
  have h1 : 1 - (1 / ((q : Nat.Primes) : ℝ)) ^ r ≠ 0 :=
    sub_ne_zero.mpr (pow_inv_q_lt_one q.1 (by omega)).ne'
  have h2 : 1 - (1 / ((q : Nat.Primes) : ℝ)) ^ 2 ≠ 0 :=
    sub_ne_zero.mpr (pow_inv_q_lt_one q.1 (by omega)).ne'
  field_simp
end FixedOrderFactor
