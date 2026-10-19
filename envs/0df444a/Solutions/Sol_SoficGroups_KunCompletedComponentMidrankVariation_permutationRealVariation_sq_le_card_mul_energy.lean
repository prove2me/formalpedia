-- Prove2me | solution 1 for SoficGroups.KunCompletedComponentMidrankVariation.permutationRealVariation_sq_le_card_mul_energy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.855273+00:00
-- url     : https://prove2.me/submissions/375f5f88-0bcf-4b07-9239-658b7c59df1a

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunCompletedComponentMidrankVariation
open Filter Topology
open scoped BigOperators
namespace SoficGroups.KunCompletedComponentMidrankVariation
theorem _root_.solution
    {V ι : Type*} [Fintype V] [Fintype ι]
    (σ : ι → Equiv.Perm V) (f : V → ℝ) :
    permutationRealVariation σ f ^ 2 ≤
      ((Fintype.card ι : ℝ) * Fintype.card V) *
        (∑ i : ι, ∑ x : V, (f (σ i x) - f x) ^ 2) := by
  classical
  have h := Finset.sum_mul_sq_le_sq_mul_sq
    (Finset.univ : Finset (ι × V))
    (fun _ : ι × V => (1 : ℝ))
    (fun z : ι × V => |f (σ z.1 z.2) - f z.2|)
  simpa only [one_mul, one_pow, sq_abs,
    ← Finset.univ_product_univ, Finset.sum_product,
    Finset.sum_const_zero, Finset.sum_const, Finset.card_product,
    Finset.card_univ, Nat.cast_mul, nsmul_eq_mul, mul_one,
    permutationRealVariation] using h
end SoficGroups.KunCompletedComponentMidrankVariation
