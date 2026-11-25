-- Prove2me | solution 1 for SinkReset.Plan.f_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:44:46.153548+00:00
-- url     : https://prove2.me/submissions/092f3148-09ab-4929-9baa-4273bf1787f9

module
public import Definitions.Def_SinkReset_Basic
public import Definitions.Def_SinkReset_Plan

set_option autoImplicit false
@[expose] public section
public section
open SinkReset
open SinkReset.Plan
namespace SinkReset.Plan
theorem _root_.solution (n : ℕ) : f 1 n = n * (n - 1) / 2 := by
  rw [← Finset.sum_range_id]
  unfold f
  refine Finset.sum_congr rfl fun i _ => ?_
  simp
end SinkReset.Plan
