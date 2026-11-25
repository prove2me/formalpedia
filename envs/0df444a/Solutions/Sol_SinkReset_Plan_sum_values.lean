-- Prove2me | solution 1 for SinkReset.Plan.sum_values
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:45:03.332881+00:00
-- url     : https://prove2.me/submissions/87e5ac44-98f9-4e0f-9eb3-3625e41118b4

module
public import Definitions.Def_SinkReset_Basic
public import Definitions.Def_SinkReset_Plan

set_option autoImplicit false
@[expose] public section
public section
open SinkReset
open SinkReset.Plan
namespace SinkReset.Plan
theorem _root_.solution (n : ℕ) :
    potential Fin.val (Finset.univ : Finset (Fin n)) = n * (n - 1) / 2 := by
  unfold potential
  rw [Fin.sum_univ_eq_sum_range (fun i => i) n, Finset.sum_range_id]
end SinkReset.Plan
