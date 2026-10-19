-- Prove2me | solution 1 for SoficGroups.KunThomFiberCoarea.natDist_sub_one_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.294654+00:00
-- url     : https://prove2.me/submissions/5000bfe4-db14-4a48-9ca4-53a4a8713116

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunThomFiberCoarea
namespace SoficGroups.KunThomFiberCoarea
theorem _root_.solution (a b : ℕ) :
    Nat.dist (a - 1) (b - 1) ≤ Nat.dist a b := by
  simp only [Nat.dist]
  omega
end SoficGroups.KunThomFiberCoarea
