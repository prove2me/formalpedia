-- Prove2me | solution 1 for P2M_FixedOrderFactor_tendsto_correctionFactor__cb9cd39b5893
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:02:19.430915+00:00
-- url     : https://prove2.me/submissions/21ff6bac-ee18-40fc-9735-a6018fa6d88e

module
public import Definitions.Def_FixedOrderFactor_Model
public import Definitions.Def_FixedOrderFactor_Order
public import Theorems.Thm_P2M_FixedOrderFactor_correctionFactor_eq_mul__b1856a05bcec
public import Theorems.Thm_FixedOrderFactor_tendsto_zetaN_empty
public import Theorems.Thm_FixedOrderFactor_inv_q_lt_one
public import Theorems.Thm_FixedOrderFactor_inv_q_pos


set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology Finset
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution (N : Finset Nat.Primes) :
    Tendsto (fun r => correctionFactor N r) atTop (𝓝 1) := by
  have h1 : Tendsto (fun r => correctionFactor ∅ r) atTop (𝓝 1) := by
    have hA := tendsto_zetaN_empty
    have hB := tendsto_zetaN_empty.comp (tendsto_id.const_mul_atTop' (by norm_num : 0 < 2))
    have := (hA.pow 2).div hB one_ne_zero
    simp only [one_pow, div_one] at this
    exact this
  have h2 : Tendsto (fun r : ℕ => ∏ q ∈ N, (1 - (1 / (q : ℝ)) ^ r) / (1 + (1 / (q : ℝ)) ^ r))
      atTop (𝓝 1) := by
    have : ∀ q ∈ N, Tendsto (fun r : ℕ => (1 - (1 / (q : ℝ)) ^ r) / (1 + (1 / (q : ℝ)) ^ r))
        atTop (𝓝 1) := by
      intro q _
      have hp := tendsto_pow_atTop_nhds_zero_of_lt_one (inv_q_pos q).le (inv_q_lt_one q)
      have := (tendsto_const_nhds (x := (1 : ℝ))).sub hp |>.div
        ((tendsto_const_nhds (x := (1 : ℝ))).add hp) (by norm_num)
      simp only [sub_zero, add_zero, div_one] at this
      exact this
    simpa using tendsto_finset_prod N this
  have := h1.mul h2
  rw [one_mul] at this
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with r hr
  exact (correctionFactor_eq_mul' N hr).symm
end FixedOrderFactor
