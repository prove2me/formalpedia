-- Prove2me | solution 1 for SmallRatio.euclid_congruence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:25:40.327541+00:00
-- url     : https://prove2.me/submissions/2ad93af4-dcbf-4e9e-99a9-892e11beed28

module
public import Definitions.Def_SmallRatio
public import Definitions.Def_SmallRatios_Solution
public import Theorems.Thm_SmallRatio_den_congr


set_option autoImplicit true
@[expose] public section
public section
open SmallRatio
open Finset
namespace SmallRatio
theorem _root_.solution (k h j : ℕ) :
    (k : ℤ) ∣ (h : ℤ) * den k h j - (-1) ^ (j + 1) * rem k h j :=
  den_congr j
end SmallRatio
