-- Prove2me | solution 1 for SoficGroups.normalizedHamming_comm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.999068+00:00
-- url     : https://prove2.me/submissions/6193f1a9-d77a-4657-8b81-ee5e794ba706

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution {Y : Type*} [Fintype Y] [DecidableEq Y]
    (p q : Equiv.Perm Y) : normalizedHamming p q = normalizedHamming q p := by
  simp only [normalizedHamming, hammingDist_comm]
end SoficGroups
