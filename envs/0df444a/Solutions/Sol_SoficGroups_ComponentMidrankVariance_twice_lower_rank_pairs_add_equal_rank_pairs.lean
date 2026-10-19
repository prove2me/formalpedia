-- Prove2me | solution 1 for SoficGroups.ComponentMidrankVariance.twice_lower_rank_pairs_add_equal_rank_pairs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.013021+00:00
-- url     : https://prove2.me/submissions/0aa40f2a-535c-44b5-b44a-9aa2739911bc

import Mathlib
import Definitions.Def_NonSoficGroup

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
    {V : Type*} (C : Finset V) (b : V → ℤ) :
    2 * (∑ x ∈ C, ((C.filter fun z => b z < b x).card : ℝ)) +
        (∑ x ∈ C, ((C.filter fun z => b z = b x).card : ℝ)) =
      (C.card : ℝ) ^ 2 := by
  classical
  let L : V → V → ℝ := fun x z => if b z < b x then 1 else 0
  let E : V → V → ℝ := fun x z => if b z = b x then 1 else 0
  have htri (x z : V) : L x z + L z x + E x z = 1 := by
    dsimp [L, E]
    split_ifs <;> norm_num <;> omega
  have hswap :
      (∑ x ∈ C, ∑ z ∈ C, L z x) =
        ∑ x ∈ C, ∑ z ∈ C, L x z := by
    rw [Finset.sum_comm]
  have hlower (x : V) :
      ((C.filter fun z => b z < b x).card : ℝ) =
        ∑ z ∈ C, L x z := by
    change ((C.filter fun z => b z < b x).card : ℝ) =
      ∑ z ∈ C, if b z < b x then 1 else 0
    exact (Finset.sum_boole (fun z : V => b z < b x) C).symm
  have hequal (x : V) :
      ((C.filter fun z => b z = b x).card : ℝ) =
        ∑ z ∈ C, E x z := by
    change ((C.filter fun z => b z = b x).card : ℝ) =
      ∑ z ∈ C, if b z = b x then 1 else 0
    exact (Finset.sum_boole (fun z : V => b z = b x) C).symm
  simp_rw [hlower, hequal]
  calc
    2 * (∑ x ∈ C, ∑ z ∈ C, L x z) +
        (∑ x ∈ C, ∑ z ∈ C, E x z) =
      ∑ x ∈ C, ∑ z ∈ C, (L x z + L z x + E x z) := by
        simp_rw [Finset.sum_add_distrib]
        rw [hswap]
        ring
    _ = ∑ x ∈ C, ∑ _z ∈ C, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro z _
      exact htri x z
    _ = (C.card : ℝ) ^ 2 := by
      simp [pow_two]
end SoficGroups.ComponentMidrankVariance
