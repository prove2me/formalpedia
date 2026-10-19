-- Prove2me | solution 1 for SoficGroups.KunThomFiberCoarea.natDist_zero_indicator_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.294654+00:00
-- url     : https://prove2.me/submissions/839ddaae-ab2f-477e-99a3-d620d8c303b0

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunThomFiberCoarea
namespace SoficGroups.KunThomFiberCoarea
theorem _root_.solution (a b : ℕ) :
    Nat.dist (if a = 0 then 1 else 0)
      (if b = 0 then 1 else 0) ≤ Nat.dist a b := by
  by_cases ha : a = 0
  · by_cases hb : b = 0
    · simp [ha, hb]
    · simp [ha, hb, Nat.dist]
      omega
  · by_cases hb : b = 0
    · simp [ha, hb, Nat.dist]
      omega
    · simp [ha, hb]
end SoficGroups.KunThomFiberCoarea
