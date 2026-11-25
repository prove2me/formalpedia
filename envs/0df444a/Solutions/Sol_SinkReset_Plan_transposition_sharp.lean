-- Prove2me | solution 1 for SinkReset.Plan.transposition_sharp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:53:04.347463+00:00
-- url     : https://prove2.me/submissions/a1bcba74-d411-4a78-9369-81e4d7af9c19

module
public import Definitions.Def_SinkReset_Basic
public import Definitions.Def_SinkReset_Plan
public import Theorems.Thm_SinkReset_Plan_one_game_iff
public import Theorems.Thm_SinkReset_Plan_f_one
public import Theorems.Thm_SinkReset_Plan_potential_bound
public import Theorems.Thm_SinkReset_Plan_transposition_step
public import Theorems.Thm_SinkReset_Plan_sum_values
public import Theorems.Thm_SinkReset_Plan_transposition_reset

set_option autoImplicit false
@[expose] public section
public section
open SinkReset
open SinkReset.Plan
namespace SinkReset.Plan
theorem _root_.solution {n : ℕ} [NeZero n] (hn : 2 ≤ n) :
    (transposition n).IsAk 1 ∧
    ∀ w, (transposition n).IsReset w → f 1 n ≤ w.length := by
  obtain ⟨w, hw, _⟩ := transposition_reset hn
  refine ⟨(one_game_iff _).2 ⟨w, hw⟩, fun w hw => ?_⟩
  rw [f_one, ← sum_values n]
  exact potential_bound _ Fin.val rfl (fun a ha S => transposition_step hn a ha S) w hw
end SinkReset.Plan
