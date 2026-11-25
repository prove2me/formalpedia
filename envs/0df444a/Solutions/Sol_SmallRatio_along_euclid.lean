-- Prove2me | solution 1 for SmallRatio.along_euclid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:40:37.824732+00:00
-- url     : https://prove2.me/submissions/ade27ba1-d0bb-4446-a3d5-04842317af74

module
public import Definitions.Def_SmallRatio
public import Definitions.Def_SmallRatios_Solution
public import Theorems.Thm_SmallRatio_dedekind_along_euclid


set_option autoImplicit true
@[expose] public section
public section
open SmallRatio
open Finset
namespace SmallRatio
theorem _root_.solution {k h : ℕ} (hh : 0 < h) (hhk : h < k) (hc : Nat.Coprime k h) :
    |12 * dedekindSum h k - ∑ i ∈ Icc 1 (steps k h),
        (-1) ^ (i + 1) * ((k : ℚ) / ((rem k h i : ℚ) * den k h i))| ≤ 4 * steps k h :=
  dedekind_along_euclid hh hhk hc
end SmallRatio
