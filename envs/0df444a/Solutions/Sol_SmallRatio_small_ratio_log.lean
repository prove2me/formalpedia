-- Prove2me | solution 1 for SmallRatio.small_ratio_log
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:44:08.952791+00:00
-- url     : https://prove2.me/submissions/7411f5a9-d132-4f74-a7ee-93e4bb75b6f9

module
public import Definitions.Def_SmallRatio
public import Definitions.Def_SmallRatios_Solution
public import Theorems.Thm_SmallRatio_small_ratio_element


set_option autoImplicit true
@[expose] public section
public section
open SmallRatio
open Finset
namespace SmallRatio
theorem _root_.solution {p h : ℕ} (hp : p.Prime) (hh : 0 < h) (hhp : h < p) :
    |12 * dedekindSum h p - p * smallRatioSum p h| ≤ 12 * Nat.log 2 p + 6 :=
  small_ratio_element hp hh hhp
end SmallRatio
