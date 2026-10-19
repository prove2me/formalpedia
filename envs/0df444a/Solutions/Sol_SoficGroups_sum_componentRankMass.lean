-- Prove2me | solution 1 for SoficGroups.sum_componentRankMass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:52.29415+00:00
-- url     : https://prove2.me/submissions/d6f79dc0-f941-4922-93cd-d7ab17582aaa

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution {V : Type*}
    (C : Finset V) (b : V → ℤ) (hC : C.Nonempty) :
    (∑ j ∈ C.image b, componentRankMass C b j) = 1 := by
  have hcard :
      (∑ j ∈ C.image b, ((C.filter fun x => b x = j).card : ℝ)) =
        (C.card : ℝ) := by
    exact_mod_cast (Finset.card_eq_sum_card_image b C).symm
  have hne : (C.card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr hC)
  simp only [componentRankMass, ← Finset.sum_div]
  rw [hcard, div_self hne]
end SoficGroups
