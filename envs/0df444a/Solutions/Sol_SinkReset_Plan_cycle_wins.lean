-- Prove2me | solution 1 for SinkReset.Plan.cycle_wins
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:51:30.181835+00:00
-- url     : https://prove2.me/submissions/0d746cdd-af3d-43d0-b0f8-c8f27c1e6c15

module
public import Definitions.Def_SinkReset_Basic
public import Definitions.Def_SinkReset_Plan
public import Theorems.Thm_SinkReset_Plan_wins_of_rank
public import Theorems.Thm_SinkReset_Plan_cycle_rank_step

set_option autoImplicit false
@[expose] public section
public section
open SinkReset
open SinkReset.Plan
namespace SinkReset.Plan
theorem _root_.solution {k m : ℕ} (hk : 1 ≤ k) (hm : 1 ≤ m) :
    (cycle k m).IsAk k :=
  wins_of_rank _ (cycleRank k m) (fun S hS => cycle_rank_step hk hm S hS) Finset.univ
end SinkReset.Plan
