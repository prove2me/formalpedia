-- Prove2me | solution 1 for SinkReset.Plan.cycle_sharp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:53:16.757593+00:00
-- url     : https://prove2.me/submissions/ca32d5c1-3b7e-4555-810a-d5a0603bd18b

module
public import Definitions.Def_SinkReset_Basic
public import Definitions.Def_SinkReset_Plan
public import Theorems.Thm_SinkReset_Plan_potential_bound
public import Theorems.Thm_SinkReset_Plan_cycle_step
public import Theorems.Thm_SinkReset_Plan_cycle_sum
public import Theorems.Thm_SinkReset_Plan_cycle_reset
public import Theorems.Thm_SinkReset_Plan_cycle_wins
public import Theorems.Thm_SinkReset_Plan_cycle_loses

set_option autoImplicit false
@[expose] public section
public section
open SinkReset
open SinkReset.Plan
namespace SinkReset.Plan
theorem _root_.solution {k m : ℕ} (hk : 1 ≤ k) (hm : 1 ≤ m) :
    (cycle k m).IsAk k ∧
    (∃ w, (cycle k m).IsReset w ∧ w.length = k + 2 * m) ∧
    (∀ w, (cycle k m).IsReset w → k + 2 * m ≤ w.length) ∧
    ¬ (cycle k m).IsAk (k + 1) := by
  refine ⟨cycle_wins hk hm, cycle_reset hk hm, fun w hw => ?_, cycle_loses hk hm⟩
  rw [← cycle_sum hk hm]
  exact potential_bound _ _ (by simp [cycleWeight]) (fun a ha S => cycle_step hk hm a ha S) w hw
end SinkReset.Plan
