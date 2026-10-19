-- Prove2me | solution 1 for SoficGroups.KunRootedIndicatorCrossing.average_normalizedIndicatorDisplacement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:56.693907+00:00
-- url     : https://prove2.me/submissions/1fae3ba0-77db-45f5-afa1-590625d84506

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunRootedIndicatorCrossing_average_permutation_indicator_displacement

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
        (∑ i, normalizedIndicatorDisplacement p f (p i)) =
      normalizedIndicatorDefect p f := by
  simp_rw [normalizedIndicatorDisplacement]
  rw [← Finset.smul_sum, smul_comm,
    average_permutation_indicator_displacement]
  rfl
end SoficGroups.KunRootedIndicatorCrossing
