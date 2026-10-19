-- Prove2me | solution 1 for SoficGroups.KunRootedIndicatorCrossing.average_permutation_indicator_displacement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:56.693907+00:00
-- url     : https://prove2.me/submissions/90c2ec00-b2ed-4b03-8b0b-e198ee14998e

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunRootedIndicatorCrossing
universe u
open Filter
open scoped BigOperators ComplexOrder InnerProductSpace Topology
namespace SoficGroups.KunRootedIndicatorCrossing
theorem _root_.solution
    {ι V : Type*} [Fintype ι] [Nonempty ι] [Fintype V]
    (p : ι → Equiv.Perm V) (f : V → ℝ) :
    (Fintype.card ι : ℂ)⁻¹ •
        (∑ i, (permutationUnitary (p i) (indicatorVector f) -
          indicatorVector f)) =
      permutationMarkov p (indicatorVector f) - indicatorVector f := by
  have hd : (Fintype.card ι : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul ℂ]
  simp [permutationMarkov, smul_sub, smul_smul, hd]
end SoficGroups.KunRootedIndicatorCrossing
