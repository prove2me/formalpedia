-- Prove2me | solution 1 for SmallRatio.euclid_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:40:30.503117+00:00
-- url     : https://prove2.me/submissions/139c42f4-1481-4d0f-b38b-7b19a6b289f6

module
public import Definitions.Def_SmallRatio
public import Definitions.Def_SmallRatios_Solution
public import Theorems.Thm_SmallRatio_steps_le_log


set_option autoImplicit true
@[expose] public section
public section
open SmallRatio
open Finset
namespace SmallRatio
theorem _root_.solution {k h : ℕ} (hh : 0 < h) (hhk : h < k) (hc : Nat.Coprime k h) :
    steps k h ≤ 2 * Nat.log 2 k + 1 :=
  steps_le_log hh hhk hc
end SmallRatio
