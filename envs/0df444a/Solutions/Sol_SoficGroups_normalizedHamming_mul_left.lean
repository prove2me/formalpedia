-- Prove2me | solution 1 for SoficGroups.normalizedHamming_mul_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.999068+00:00
-- url     : https://prove2.me/submissions/60f7dcfd-ff63-42c9-a619-3ea173ef75b9

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
    (s p q : Equiv.Perm Y) :
    normalizedHamming (s * p) (s * q) = normalizedHamming p q := by
  have hdist :
      hammingDist (fun y => s (p y)) (fun y => s (q y)) =
        hammingDist (fun y => p y) (fun y => q y) :=
    hammingDist_comp (fun (_ : Y) (z : Y) => s z) (fun _ => s.injective)
  simp [normalizedHamming, Equiv.Perm.mul_apply, hdist]
end SoficGroups
