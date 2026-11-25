-- Prove2me | solution 1 for SmallRatio.euclid_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:34:27.678905+00:00
-- url     : https://prove2.me/submissions/8c2672ec-d70a-481e-8ed2-5eb544e6ad46

module
public import Definitions.Def_SmallRatio
public import Definitions.Def_SmallRatios_Solution
public import Theorems.Thm_SmallRatio_rem_den_identity


set_option autoImplicit true
@[expose] public section
public section
open SmallRatio
open Finset
namespace SmallRatio
theorem _root_.solution {k h : ℕ} (hh : 0 < h) (hhk : h < k) (hc : Nat.Coprime k h) :
    ∀ j ≤ steps k h, rem k h j * den k h (j + 1) + rem k h (j + 1) * den k h j = k :=
  fun _ hj => rem_den_identity hh hhk hc hj
end SmallRatio
