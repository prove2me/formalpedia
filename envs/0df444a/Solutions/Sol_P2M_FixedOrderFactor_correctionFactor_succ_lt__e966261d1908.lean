-- Prove2me | solution 1 for P2M_FixedOrderFactor_correctionFactor_succ_lt__e966261d1908
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:03:41.913306+00:00
-- url     : https://prove2.me/submissions/d5183a3b-e611-4eb3-bf99-21b9112496ff

module
public import Definitions.Def_FixedOrderFactor_Model
public import Definitions.Def_FixedOrderFactor_Order
public import Theorems.Thm_FixedOrderFactor_hasProd_le_of_le_one
public import Theorems.Thm_FixedOrderFactor_exists_prime_not_mem
public import Theorems.Thm_FixedOrderFactor_correctionFactor_pos
public import Theorems.Thm_FixedOrderFactor_inv_q_lt_one
public import Theorems.Thm_FixedOrderFactor_inv_q_pos
public import Theorems.Thm_P2M_FixedOrderFactor_hasProd_correctionFactor__ac45d6c11465


set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology Finset
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution (N : Finset Nat.Primes) {r : ℕ} (hr : 2 ≤ r) :
    correctionFactor N (r + 1) < correctionFactor N r := by
  classical
  obtain ⟨q₀, hq₀⟩ := exists_prime_not_mem N
  have hA := hasProd_correctionFactor' N (by omega : 2 ≤ r + 1)
  have hB := (hasProd_correctionFactor' N hr).inv₀ (correctionFactor_pos N hr).ne'
  have h := hA.mul hB
  set g : {q : Nat.Primes // q ∉ N} → ℝ := fun q =>
    (1 + (1 / (q : ℝ)) ^ (r + 1)) / (1 - (1 / (q : ℝ)) ^ (r + 1)) *
      ((1 + (1 / (q : ℝ)) ^ r) / (1 - (1 / (q : ℝ)) ^ r))⁻¹
  have hg : ∀ q, 0 < g q ∧ g q < 1 := by
    intro q
    set x := 1 / ((q : Nat.Primes) : ℝ)
    have hx0 : 0 < x := inv_q_pos q.1
    have hx1 : x < 1 := inv_q_lt_one q.1
    have hy0 : 0 < x ^ r := pow_pos hx0 r
    have hy1 : x ^ r < 1 := pow_lt_one₀ hx0.le hx1 (by omega)
    have hyy : x ^ (r + 1) < x ^ r := pow_lt_pow_right_of_lt_one₀ hx0 hx1 (by omega)
    have hz0 : 0 < x ^ (r + 1) := pow_pos hx0 _
    have hz1 : x ^ (r + 1) < 1 := lt_trans hyy hy1
    have hd1 : 0 < 1 - x ^ r := by linarith
    have hd2 : 0 < 1 - x ^ (r + 1) := by linarith
    constructor
    · show 0 < (1 + x ^ (r + 1)) / (1 - x ^ (r + 1)) * ((1 + x ^ r) / (1 - x ^ r))⁻¹
      positivity
    · show (1 + x ^ (r + 1)) / (1 - x ^ (r + 1)) * ((1 + x ^ r) / (1 - x ^ r))⁻¹ < 1
      rw [inv_div, div_mul_div_comm, div_lt_one (by positivity)]
      nlinarith
  have hle := hasProd_le_of_le_one h (fun q => (hg q).1.le) (fun q => (hg q).2.le) ⟨q₀, hq₀⟩
  have hlt := lt_of_le_of_lt hle (hg ⟨q₀, hq₀⟩).2
  have hpos := correctionFactor_pos N hr
  rwa [← div_eq_mul_inv, div_lt_one hpos] at hlt
end FixedOrderFactor
