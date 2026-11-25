-- Prove2me | solution 1 for SmallRatio.sum_over_set
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:25:58.379813+00:00
-- url     : https://prove2.me/submissions/29764db9-bf8e-402f-a419-cad3851d99f9

module
public import Definitions.Def_SmallRatio
public import Definitions.Def_SmallRatios_Solution
public import Theorems.Thm_SmallRatio_sum_smallRatioSum


set_option autoImplicit true
@[expose] public section
public section
open SmallRatio
open Finset
namespace SmallRatio
theorem _root_.solution {p : ℕ} (hp : p.Prime) (H : Finset (ZMod p)) :
    ∑ x ∈ H, smallRatioSum p x.val = subgroupSmallRatio p H :=
  sum_smallRatioSum hp H
end SmallRatio
