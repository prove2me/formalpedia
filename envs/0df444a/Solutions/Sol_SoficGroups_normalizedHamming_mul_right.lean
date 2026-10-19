-- Prove2me | solution 1 for SoficGroups.normalizedHamming_mul_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.999068+00:00
-- url     : https://prove2.me/submissions/1f5af7a0-4430-49be-b605-9a3663abe91f

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
    normalizedHamming (p * s) (q * s) = normalizedHamming p q := by
  have hdist :
      hammingDist (fun y => (p * s) y) (fun y => (q * s) y) =
        hammingDist (fun y => p y) (fun y => q y) := by
    unfold hammingDist
    apply Finset.card_bij (fun y _ => s y)
    · intro y hy
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      simpa only [Equiv.Perm.mul_apply] using (Finset.mem_filter.mp hy).2
    · intro y hy z hz h
      exact s.injective h
    · intro y hy
      refine ⟨s.symm y, ?_, by simp⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      simpa only [Equiv.Perm.mul_apply, Equiv.apply_symm_apply] using
        (Finset.mem_filter.mp hy).2
  unfold normalizedHamming
  exact congrArg
    (fun k : ℕ => (k : ℝ) / (Fintype.card Y : ℝ)) hdist
end SoficGroups
