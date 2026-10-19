-- Prove2me | solution 1 for SoficGroups.KunThomFiberCoarea.permutationVariation_subtract_layer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.294654+00:00
-- url     : https://prove2.me/submissions/5c257c12-3758-45c2-a944-c1d1451ae68a

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunThomFiberCoarea_card_entering_eq_card_exiting
import Theorems.Thm_SoficGroups_KunThomFiberCoarea_sum_indicator_nat_eq_mul_card

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunThomFiberCoarea
namespace SoficGroups.KunThomFiberCoarea
theorem _root_.solution
    {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (f : V → ℕ)
    (A : Finset V) (m : ℕ)
    (hinside : ∀ x ∈ A, m ≤ f x)
    (houtside : ∀ x, x ∉ A → f x = 0) :
    permutationVariation σ f =
      permutationVariation σ
          (fun x => if x ∈ A then f x - m else 0) +
        2 * m * SoficGroups.boundary σ A := by
  classical
  let g : V → ℕ := fun x => if x ∈ A then f x - m else 0
  have hpair (i : ι) (x : V) :
      Nat.dist (f (σ i x)) (f x) =
        Nat.dist (g (σ i x)) (g x) +
          (if x ∈ A ∧ σ i x ∉ A then m else 0) +
          (if x ∉ A ∧ σ i x ∈ A then m else 0) := by
    by_cases hx : x ∈ A
    · by_cases hy : σ i x ∈ A
      · have hxlow := hinside x hx
        have hylow := hinside (σ i x) hy
        simp [g, hx, hy, Nat.dist]
        omega
      · have hyzero := houtside (σ i x) hy
        have hxlow := hinside x hx
        simp [g, hx, hy, hyzero, Nat.dist]
        omega
    · by_cases hy : σ i x ∈ A
      · have hxzero := houtside x hx
        have hylow := hinside (σ i x) hy
        simp [g, hx, hy, hxzero, Nat.dist]
        omega
      · simp [g, hx, hy, houtside x hx,
          houtside (σ i x) hy]
  have hone (i : ι) :
      (∑ x : V, Nat.dist (f (σ i x)) (f x)) =
        (∑ x : V, Nat.dist (g (σ i x)) (g x)) +
          2 * m * (A.filter fun x => σ i x ∉ A).card := by
    have hexit :
        (∑ x : V, if x ∈ A ∧ σ i x ∉ A then m else 0) =
          m * (A.filter fun x => σ i x ∉ A).card := by
      have hset :
          Finset.univ.filter
              (fun x : V => x ∈ A ∧ σ i x ∉ A) =
            A.filter fun x => σ i x ∉ A := by
        ext x
        simp
      simpa only [hset] using
        sum_indicator_nat_eq_mul_card Finset.univ
          (fun x : V => x ∈ A ∧ σ i x ∉ A) m
    have henter :
        (∑ x : V, if x ∉ A ∧ σ i x ∈ A then m else 0) =
          m * (Finset.univ.filter fun x =>
            x ∉ A ∧ σ i x ∈ A).card :=
      sum_indicator_nat_eq_mul_card
        Finset.univ (fun x => x ∉ A ∧ σ i x ∈ A) m
    calc
      (∑ x : V, Nat.dist (f (σ i x)) (f x)) =
          ∑ x : V,
            (Nat.dist (g (σ i x)) (g x) +
              (if x ∈ A ∧ σ i x ∉ A then m else 0) +
              (if x ∉ A ∧ σ i x ∈ A then m else 0)) := by
            apply Finset.sum_congr rfl
            intro x _
            exact hpair i x
      _ = (∑ x : V, Nat.dist (g (σ i x)) (g x)) +
            (∑ x : V, if x ∈ A ∧ σ i x ∉ A then m else 0) +
            (∑ x : V, if x ∉ A ∧ σ i x ∈ A then m else 0) := by
            simp_rw [Finset.sum_add_distrib]
      _ = (∑ x : V, Nat.dist (g (σ i x)) (g x)) +
            m * (A.filter fun x => σ i x ∉ A).card +
            m * (Finset.univ.filter fun x =>
              x ∉ A ∧ σ i x ∈ A).card := by
            rw [hexit, henter]
      _ = (∑ x : V, Nat.dist (g (σ i x)) (g x)) +
            2 * m * (A.filter fun x => σ i x ∉ A).card := by
            rw [card_entering_eq_card_exiting]
            ring
  unfold permutationVariation SoficGroups.boundary
  calc
    (∑ i : ι, ∑ x : V, Nat.dist (f (σ i x)) (f x)) =
        ∑ i : ι,
          ((∑ x : V, Nat.dist (g (σ i x)) (g x)) +
            2 * m * (A.filter fun x => σ i x ∉ A).card) := by
          apply Finset.sum_congr rfl
          intro i _
          exact hone i
    _ = (∑ i : ι, ∑ x : V,
          Nat.dist (g (σ i x)) (g x)) +
          2 * m *
            ∑ i : ι, (A.filter fun x => σ i x ∉ A).card := by
          simp [Finset.sum_add_distrib, Finset.mul_sum]
end SoficGroups.KunThomFiberCoarea
