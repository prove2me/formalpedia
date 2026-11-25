-- Prove2me | solution 1 for SmallRatio.euclid_terminates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:35:07.448991+00:00
-- url     : https://prove2.me/submissions/1ce35351-777e-464b-9ddf-7573b25ecbca

module
public import Definitions.Def_SmallRatio
public import Definitions.Def_SmallRatios_Solution
public import Theorems.Thm_SmallRatio_rem_steps
public import Theorems.Thm_SmallRatio_rem_strictAnti
public import Theorems.Thm_SmallRatio_two_le_rem_of_lt_steps


set_option autoImplicit true
@[expose] public section
public section
open SmallRatio
open Finset
namespace SmallRatio
theorem _root_.solution {k h : ℕ} (hh : 0 < h) (hhk : h < k) (hc : Nat.Coprime k h) :
    rem k h (steps k h) = 1 ∧ (∀ j < steps k h, 2 ≤ rem k h j) ∧
      ∀ i j, i < j → j ≤ steps k h → rem k h j < rem k h i :=
  ⟨rem_steps hh hhk hc, fun _ hj => two_le_rem_of_lt_steps hj,
    fun _ _ hij hj => rem_strictAnti hh hhk hc hij hj⟩
end SmallRatio
