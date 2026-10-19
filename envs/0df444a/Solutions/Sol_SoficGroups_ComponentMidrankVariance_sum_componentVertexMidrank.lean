-- Prove2me | solution 1 for SoficGroups.ComponentMidrankVariance.sum_componentVertexMidrank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.013021+00:00
-- url     : https://prove2.me/submissions/015dcafd-c771-493d-8959-9509d1a00ded

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_ComponentMidrankVariance_twice_lower_rank_pairs_add_equal_rank_pairs

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
open SoficGroups.ComponentMidrankVariance
open scoped BigOperators
namespace SoficGroups.ComponentMidrankVariance
theorem _root_.solution
    {V : Type*}
    (C : Finset V) (b : V → ℤ) (hC : C.Nonempty) :
    (∑ x ∈ C, SoficGroups.componentVertexMidrank C b x) =
      (C.card : ℝ) / 2 := by
  have hcard : (C.card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hC
  have hpairs := twice_lower_rank_pairs_add_equal_rank_pairs C b
  unfold SoficGroups.componentVertexMidrank
  rw [← Finset.sum_div]
  have hnum :
      (∑ x ∈ C,
        (((C.filter fun z => b z < b x).card : ℝ) +
          ((C.filter fun z => b z = b x).card : ℝ) / 2)) =
        (C.card : ℝ) ^ 2 / 2 := by
    rw [Finset.sum_add_distrib, ← Finset.sum_div]
    linarith
  rw [hnum]
  field_simp
end SoficGroups.ComponentMidrankVariance
