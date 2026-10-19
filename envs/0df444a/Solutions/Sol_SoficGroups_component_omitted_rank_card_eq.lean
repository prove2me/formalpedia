-- Prove2me | solution 1 for SoficGroups.component_omitted_rank_card_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:52.29415+00:00
-- url     : https://prove2.me/submissions/cf45c0f0-7d83-4e00-8901-924f2098f8d8

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution
    {V : Type*}
    (C : Finset V) (b : V → ℤ) (j : ℤ)
    (hC : C.Nonempty) :
    ((C.card - (C.filter fun x => b x = j).card : ℕ) : ℝ) =
      (C.card : ℝ) * (1 - componentRankMass C b j) := by
  have hsub : (C.filter fun x => b x = j).card ≤ C.card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  have hne : (C.card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hC
  rw [Nat.cast_sub hsub]
  unfold componentRankMass
  field_simp [hne]
end SoficGroups
