-- Prove2me | solution 1 for SinkReset.Plan.f_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:44:49.952148+00:00
-- url     : https://prove2.me/submissions/ac7829b2-b414-4082-8daa-de8181eac9ae

module
public import Definitions.Def_SinkReset_Basic
public import Definitions.Def_SinkReset_Plan

set_option autoImplicit false
@[expose] public section
public section
open SinkReset
open SinkReset.Plan
namespace SinkReset.Plan
theorem _root_.solution {k c d : ℕ} (hk : 1 ≤ k) :
    f k (c + 1) + f k (d + 1) ≤ f k (c + d + 1) := by
  have h1 : f k (c + d + 1) = f k (d + 1) + ∑ x ∈ Finset.range c, (d + 1 + x + k - 1) / k := by
    rw [show c + d + 1 = (d + 1) + c by omega]
    unfold f
    exact Finset.sum_range_add _ _ _
  have h2 : f k (c + 1) = ∑ x ∈ Finset.range c, (x + 1 + k - 1) / k := by
    unfold f
    rw [Finset.sum_range_succ']
    simp only [zero_add, add_eq_left]
    exact Nat.div_eq_of_lt (by omega)
  rw [h1, h2, add_comm]
  refine Nat.add_le_add_left (Finset.sum_le_sum fun x _ => Nat.div_le_div_right (by omega)) _
end SinkReset.Plan
