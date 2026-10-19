-- Prove2me | solution 1 for SoficGroups.KunCompletedComponentMidrankVariation.completed_component_real_variation_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.855273+00:00
-- url     : https://prove2.me/submissions/fd31ba97-4f56-45c6-9fa6-dd37c89553e9

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
    {V ι : Type*} [DecidableEq V] [Fintype ι]
    (σ : ι → Equiv.Perm V)
    (C : Finset V)
    (τ : ι → Equiv.Perm {x : V // x ∈ C})
    (hτ : ∀ i (x : V) (hx : x ∈ C) (_hy : σ i x ∈ C),
      ((τ i ⟨x, hx⟩ : {x : V // x ∈ C}) : V) = σ i x)
    (f : V → ℝ)
    (hf0 : ∀ x, 0 ≤ f x)
    (hf1 : ∀ x, f x ≤ 1) :
    permutationRealVariation τ (fun x => f (x : V)) ≤
      (∑ i : ι, ∑ x ∈ C, |f (σ i x) - f x|) +
        (SoficGroups.boundary σ C : ℝ) := by
  classical
  have hunit (x y : V) : |f x - f y| ≤ (1 : ℝ) := by
    apply (abs_le).2
    constructor <;> linarith [hf0 x, hf0 y, hf1 x, hf1 y]
  have hpoint (i : ι) (x : {x : V // x ∈ C}) :
      |f ((τ i x : {x : V // x ∈ C}) : V) - f (x : V)| ≤
        |f (σ i (x : V)) - f (x : V)| +
          if σ i (x : V) ∈ C then 0 else 1 := by
    by_cases hinside : σ i (x : V) ∈ C
    · simp only [if_pos hinside, add_zero]
      rw [hτ i (x : V) x.property hinside]
    · simp only [if_neg hinside]
      linarith [hunit
        ((τ i x : {x : V // x ∈ C}) : V) (x : V),
        abs_nonneg (f (σ i (x : V)) - f (x : V))]
  calc
    permutationRealVariation τ (fun x => f (x : V)) ≤
        ∑ i : ι, ∑ x : {x : V // x ∈ C},
          (|f (σ i (x : V)) - f (x : V)| +
            if σ i (x : V) ∈ C then 0 else 1) := by
          unfold permutationRealVariation
          apply Finset.sum_le_sum
          intro i _
          apply Finset.sum_le_sum
          intro x _
          exact hpoint i x
    _ = ∑ i : ι,
          ((∑ x ∈ C, |f (σ i x) - f x|) +
            ((C.filter fun x => σ i x ∉ C).card : ℝ)) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_add_distrib]
          have horiginal :
              (∑ x : {x : V // x ∈ C},
                |f (σ i (x : V)) - f (x : V)|) =
                ∑ x ∈ C, |f (σ i x) - f x| :=
            (Finset.sum_subtype C (fun _ => Iff.rfl)
              (fun x : V => |f (σ i x) - f x|)).symm
          have hmiss :
              (∑ x : {x : V // x ∈ C},
                if σ i (x : V) ∈ C then (0 : ℝ) else 1) =
                ((C.filter fun x => σ i x ∉ C).card : ℝ) := by
            calc
              (∑ x : {x : V // x ∈ C},
                if σ i (x : V) ∈ C then (0 : ℝ) else 1) =
                  ∑ x ∈ C,
                    if σ i x ∈ C then (0 : ℝ) else 1 :=
                (Finset.sum_subtype C (fun _ => Iff.rfl)
                  (fun x : V => if σ i x ∈ C then (0 : ℝ) else 1)).symm
              _ = ((C.filter fun x => σ i x ∉ C).card : ℝ) := by
                simpa only [ite_not] using
                  (Finset.sum_boole (R := ℝ)
                    (fun x : V => σ i x ∉ C) C)
          rw [horiginal, hmiss]
    _ = (∑ i : ι, ∑ x ∈ C, |f (σ i x) - f x|) +
          (SoficGroups.boundary σ C : ℝ) := by
          simp [SoficGroups.boundary, Finset.sum_add_distrib]
end SoficGroups.KunCompletedComponentMidrankVariation
