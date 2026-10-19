-- Prove2me | solution 1 for SoficGroups.normalizedHamming_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.999068+00:00
-- url     : https://prove2.me/submissions/d4c707d6-636c-415d-b3eb-7face7886aff

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
    (p q : Equiv.Perm Y) : 0 ≤ normalizedHamming p q := by
  unfold normalizedHamming
  positivity
end SoficGroups
