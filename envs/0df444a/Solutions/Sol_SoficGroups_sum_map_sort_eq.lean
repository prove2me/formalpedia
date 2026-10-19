-- Prove2me | solution 1 for SoficGroups.sum_map_sort_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:52.29415+00:00
-- url     : https://prove2.me/submissions/6a467925-6e9b-4d00-8bd1-59190957af16

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution {α : Type*}
    [LinearOrder α]
    (s : Finset α) (f : α → ℝ) :
    ((s.sort (· ≤ ·)).map f).sum = ∑ a ∈ s, f a := by
  change
    ((s.sort (· ≤ ·)).map f).sum =
      (s.val.map f).sum
  have h := congrArg
    (fun t : Multiset α => (t.map f).sum)
    (s.sort_eq (· ≤ ·))
  simpa only [Multiset.map_coe, Multiset.sum_coe] using h
end SoficGroups
