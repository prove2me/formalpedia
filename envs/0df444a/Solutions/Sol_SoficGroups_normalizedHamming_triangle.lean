-- Prove2me | solution 1 for SoficGroups.normalizedHamming_triangle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.999068+00:00
-- url     : https://prove2.me/submissions/90c7a78b-1c34-47b3-822e-3dd26f5624e1

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
    (p q r : Equiv.Perm Y) :
    normalizedHamming p r ≤ normalizedHamming p q + normalizedHamming q r := by
  have h := hammingDist_triangle (fun y => p y) (fun y => q y) (fun y => r y)
  unfold normalizedHamming
  rw [← add_div]
  apply div_le_div_of_nonneg_right
  · exact_mod_cast h
  · positivity
end SoficGroups
