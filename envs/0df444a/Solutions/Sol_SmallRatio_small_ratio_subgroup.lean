-- Prove2me | solution 1 for SmallRatio.small_ratio_subgroup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:46:16.201207+00:00
-- url     : https://prove2.me/submissions/c28cfe22-c8e3-4fb3-ba65-003f85ee4b77

module
public import Definitions.Def_SmallRatio
public import Definitions.Def_SmallRatios_Solution
public import Theorems.Thm_SmallRatio_small_ratio_set


set_option autoImplicit true
@[expose] public section
public section
open SmallRatio
open Finset
namespace SmallRatio
theorem _root_.solution {p : ℕ} (hp : p.Prime) (H : Finset (ZMod p)) :
    |12 * ∑ x ∈ H, dedekindSum x.val p - p * subgroupSmallRatio p H| ≤
      H.card * (12 * Nat.log 2 p + 6) :=
  small_ratio_set hp H
end SmallRatio
