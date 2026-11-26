-- Prove2me | solution 1 for P2M_FixedOrderFactor_one_lt_correctionFactor__3ccb13979d24
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:01:03.03594+00:00
-- url     : https://prove2.me/submissions/a3013fd8-12ca-43a9-872c-6cc0d229d672

module
public import Definitions.Def_FixedOrderFactor_Model
public import Definitions.Def_FixedOrderFactor_Order
public import Theorems.Thm_FixedOrderFactor_le_of_hasProd_one_le
public import Theorems.Thm_FixedOrderFactor_exists_prime_not_mem
public import Theorems.Thm_FixedOrderFactor_factor_gt_one
public import Theorems.Thm_FixedOrderFactor_inv_q_pos
public import Theorems.Thm_FixedOrderFactor_pow_inv_q_lt_one
public import Theorems.Thm_P2M_FixedOrderFactor_hasProd_correctionFactor__ac45d6c11465


set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology Finset
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution (N : Finset Nat.Primes) {r : ℕ} (hr : 2 ≤ r) :
    1 < correctionFactor N r := by
  classical
  obtain ⟨q₀, hq₀⟩ := exists_prime_not_mem N
  have h := hasProd_correctionFactor' N hr
  have hf : ∀ q : {q : Nat.Primes // q ∉ N}, 1 < (1 + (1 / (q : ℝ)) ^ r) / (1 - (1 / (q : ℝ)) ^ r) :=
    fun q => factor_gt_one (pow_pos (inv_q_pos q.1) r) (pow_inv_q_lt_one q.1 (by omega))
  exact lt_of_lt_of_le (hf ⟨q₀, hq₀⟩) (le_of_hasProd_one_le h (fun q => (hf q).le) ⟨q₀, hq₀⟩)
end FixedOrderFactor
