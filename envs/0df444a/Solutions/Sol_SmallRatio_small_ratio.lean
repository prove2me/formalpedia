-- Prove2me | solution 1 for SmallRatio.small_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:41:39.741942+00:00
-- url     : https://prove2.me/submissions/dea0ff90-d5ec-468c-9558-08cc7a273a09

module
public import Definitions.Def_SmallRatio
public import Definitions.Def_SmallRatios_Solution
public import Theorems.Thm_SmallRatio_small_ratio_steps


set_option autoImplicit true
@[expose] public section
public section
open SmallRatio
open Finset
namespace SmallRatio
theorem _root_.solution {p h : ℕ} (hp : p.Prime) (hh : 0 < h) (hhp : h < p) :
    |12 * dedekindSum h p - p * smallRatioSum p h| ≤ 6 * steps p h :=
  small_ratio_steps hp hh hhp
end SmallRatio
