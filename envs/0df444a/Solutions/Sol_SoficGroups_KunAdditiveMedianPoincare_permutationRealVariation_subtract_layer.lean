-- Prove2me | solution 1 for SoficGroups.KunAdditiveMedianPoincare.permutationRealVariation_subtract_layer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.855273+00:00
-- url     : https://prove2.me/submissions/ea63aa14-4960-4256-8eb3-e693ace08b75

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunThomFiberCoarea_card_entering_eq_card_exiting
import Theorems.Thm_SoficGroups_KunAdditiveMedianPoincare_sum_indicator_real_eq_mul_card

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunAdditiveMedianPoincare
open SoficGroups.CheegerPoincare
open Filter Topology
open scoped BigOperators
namespace SoficGroups.KunAdditiveMedianPoincare
theorem _root_.solution
    {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (f : V → ℝ)
    (A : Finset V) (m : ℝ) (hm : 0 ≤ m)
    (hinside : ∀ x ∈ A, m ≤ f x)
    (houtside : ∀ x, x ∉ A → f x = 0) :
    permutationRealVariation σ f =
      permutationRealVariation σ
        (fun x => if x ∈ A then f x - m else 0) +
        2 * m * (SoficGroups.boundary σ A : ℝ) := by
  classical
  let g : V → ℝ := fun x => if x ∈ A then f x - m else 0
  have hpair (i : ι) (x : V) :
      |f (σ i x) - f x| =
        |g (σ i x) - g x| +
          (if x ∈ A ∧ σ i x ∉ A then m else 0) +
          (if x ∉ A ∧ σ i x ∈ A then m else 0) := by
    by_cases hx : x ∈ A
    · by_cases hy : σ i x ∈ A
      · simp [g, hx, hy, sub_sub_sub_cancel_right]
      · have hyzero := houtside (σ i x) hy
        have hxnonnegative : 0 ≤ f x := hm.trans (hinside x hx)
        simp [g, hx, hy, hyzero,
          abs_of_nonneg hxnonnegative,
          abs_of_nonpos (sub_nonpos.mpr (hinside x hx))]
    · by_cases hy : σ i x ∈ A
      · have hxzero := houtside x hx
        have hynonnegative : 0 ≤ f (σ i x) :=
          hm.trans (hinside (σ i x) hy)
        have hysub : 0 ≤ f (σ i x) - m :=
          sub_nonneg.mpr (hinside (σ i x) hy)
        simp [g, hx, hy, hxzero,
          abs_of_nonneg hynonnegative, abs_of_nonneg hysub]
      · simp [g, hx, hy, houtside x hx,
          houtside (σ i x) hy]
  have hone (i : ι) :
      (∑ x : V, |f (σ i x) - f x|) =
        (∑ x : V, |g (σ i x) - g x|) +
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
        sum_indicator_real_eq_mul_card Finset.univ
          (fun x : V => x ∈ A ∧ σ i x ∉ A) m
    have henter :
        (∑ x : V, if x ∉ A ∧ σ i x ∈ A then m else 0) =
          m * (Finset.univ.filter fun x =>
            x ∉ A ∧ σ i x ∈ A).card :=
      sum_indicator_real_eq_mul_card
        Finset.univ (fun x => x ∉ A ∧ σ i x ∈ A) m
    calc
      (∑ x : V, |f (σ i x) - f x|) =
          ∑ x : V,
            (|g (σ i x) - g x| +
              (if x ∈ A ∧ σ i x ∉ A then m else 0) +
              (if x ∉ A ∧ σ i x ∈ A then m else 0)) := by
            apply Finset.sum_congr rfl
            intro x _
            exact hpair i x
      _ = (∑ x : V, |g (σ i x) - g x|) +
            (∑ x : V,
              if x ∈ A ∧ σ i x ∉ A then m else 0) +
            (∑ x : V,
              if x ∉ A ∧ σ i x ∈ A then m else 0) := by
            simp_rw [Finset.sum_add_distrib]
      _ = (∑ x : V, |g (σ i x) - g x|) +
            m * (A.filter fun x => σ i x ∉ A).card +
            m * (Finset.univ.filter fun x =>
              x ∉ A ∧ σ i x ∈ A).card := by
            rw [hexit, henter]
      _ = (∑ x : V, |g (σ i x) - g x|) +
            2 * m * (A.filter fun x => σ i x ∉ A).card := by
            have hcross :
                (Finset.univ.filter fun x =>
                  x ∉ A ∧ σ i x ∈ A).card =
                  (A.filter fun x => σ i x ∉ A).card :=
              SoficGroups.KunThomFiberCoarea.card_entering_eq_card_exiting
                (σ i) A
            rw [hcross]
            ring
  unfold permutationRealVariation SoficGroups.boundary
  calc
    (∑ i : ι, ∑ x : V, |f (σ i x) - f x|) =
        ∑ i : ι,
          ((∑ x : V, |g (σ i x) - g x|) +
            2 * m * (A.filter fun x => σ i x ∉ A).card) := by
          apply Finset.sum_congr rfl
          intro i _
          exact hone i
    _ = (∑ i : ι, ∑ x : V, |g (σ i x) - g x|) +
          2 * m *
            (∑ i : ι, (A.filter fun x => σ i x ∉ A).card) := by
          push_cast
          simp [Finset.sum_add_distrib, Finset.mul_sum]
end SoficGroups.KunAdditiveMedianPoincare
