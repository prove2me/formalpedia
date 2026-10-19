-- Prove2me | solution 1 for SoficGroups.KunPositiveWordMidrankEnergy.squaredPermutationEnergy_le_add_hammingDist
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.855273+00:00
-- url     : https://prove2.me/submissions/1d6b6fa9-6a24-49ec-952e-059cd8770258

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
    {V : Type*} [Fintype V] [DecidableEq V]
    (f : V → ℝ) (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1)
    (p q : Equiv.Perm V) :
    squaredPermutationEnergy f p ≤
      squaredPermutationEnergy f q +
        (hammingDist (fun x => p x) (fun x => q x) : ℝ) := by
  classical
  have hpoint (x : V) :
      (f (p x) - f x) ^ 2 ≤
        (f (q x) - f x) ^ 2 +
          if p x = q x then 0 else 1 := by
    split_ifs with hx
    · simp only [hx, add_zero, le_refl]
    · have hp0 := hf0 (p x)
      have hp1 := hf1 (p x)
      have hx0 := hf0 x
      have hx1 := hf1 x
      nlinarith [sq_nonneg (f (q x) - f x),
        mul_nonneg
          (show 0 ≤ 1 - (f (p x) - f x) by linarith)
          (show 0 ≤ 1 + (f (p x) - f x) by linarith)]
  have hindicator :
      (∑ x : V, if p x = q x then (0 : ℝ) else 1) =
        (hammingDist (fun x => p x) (fun x => q x) : ℝ) := by
    have hswitch (x : V) :
        (if p x = q x then (0 : ℝ) else 1) =
          if p x ≠ q x then 1 else 0 := by
      split_ifs <;> simp_all
    simp_rw [hswitch]
    simpa [hammingDist] using
      (Finset.sum_boole
        (fun x : V => p x ≠ q x) (Finset.univ : Finset V))
  unfold squaredPermutationEnergy
  calc
    (∑ x : V, (f (p x) - f x) ^ 2) ≤
        ∑ x : V,
          ((f (q x) - f x) ^ 2 +
            if p x = q x then 0 else 1) :=
      Finset.sum_le_sum fun x _ => hpoint x
    _ = (∑ x : V, (f (q x) - f x) ^ 2) +
          (hammingDist (fun x => p x) (fun x => q x) : ℝ) := by
      rw [Finset.sum_add_distrib, hindicator]
end SoficGroups.KunPositiveWordMidrankEnergy
