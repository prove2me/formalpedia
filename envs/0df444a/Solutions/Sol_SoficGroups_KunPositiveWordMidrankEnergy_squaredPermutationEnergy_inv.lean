-- Prove2me | solution 1 for SoficGroups.KunPositiveWordMidrankEnergy.squaredPermutationEnergy_inv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.855273+00:00
-- url     : https://prove2.me/submissions/f10e68bf-f5d7-41c0-8dc1-58bf1392cf42

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunPositiveWordMidrankEnergy
open Filter Topology
open scoped BigOperators
namespace SoficGroups.KunPositiveWordMidrankEnergy
theorem _root_.solution
    {V : Type*} [Fintype V] (f : V → ℝ) (p : Equiv.Perm V) :
    squaredPermutationEnergy f p⁻¹ = squaredPermutationEnergy f p := by
  unfold squaredPermutationEnergy
  calc
    (∑ x : V, (f (p⁻¹ x) - f x) ^ 2) =
        ∑ x : V, (f x - f (p x)) ^ 2 := by
          simpa using
            (Equiv.sum_comp p
              (fun x : V => (f (p⁻¹ x) - f x) ^ 2)).symm
    _ = ∑ x : V, (f (p x) - f x) ^ 2 := by
      apply Finset.sum_congr rfl
      intro x _
      ring
end SoficGroups.KunPositiveWordMidrankEnergy
