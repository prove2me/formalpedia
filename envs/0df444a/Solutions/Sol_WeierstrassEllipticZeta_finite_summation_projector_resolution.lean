-- Prove2me | solution 1 for WeierstrassEllipticZeta.finite_summation_projector_resolution
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-10T17:01:38.683369+00:00
-- url     : https://prove2.me/submissions/1877de28-3d08-4058-8af2-4c6061462f0e

import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.Ring.Idempotent

open scoped Classical



theorem solution
    (R M ι : Type*) [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι]
    (E : ι → Submodule R M) (e : (∀ i, E i) ≃ₗ[R] M)
    (he : ∀ x, e x = ∑ i, (x i : M)) :
    ∃ P : ι → Module.End R M,
      (∀ i x, P i x = (e.symm x i : M)) ∧
      (∀ i, IsIdempotentElem (P i)) ∧
      (∀ i j, i ≠ j → P i * P j = 0) ∧
      (∑ i, P i) = 1 ∧
      (∀ i, LinearMap.range (P i) = E i) ∧
      ∀ g : Module.End R M, (∀ i, Set.MapsTo g (E i) (E i)) →
        ∀ i, Commute (P i) g := by
  classical
  let P : ι → Module.End R M := fun i =>
    (E i).subtype.comp ((LinearMap.proj i).comp e.symm.toLinearMap)
  have hP (i : ι) (x : M) : P i x = (e.symm x i : M) := rfl
  have hsingle (i : ι) (x : E i) : e (Pi.single i x) = (x : M) := by
    rw [he, Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [Pi.single_eq_of_ne hji]
    · simp
  have hcoord (i : ι) (x : E i) : e.symm (x : M) = Pi.single i x := by
    apply e.injective
    rw [e.apply_symm_apply, hsingle]
  have hfix (i : ι) (x : E i) : P i (x : M) = x := by
    rw [hP, hcoord]
    simp
  refine ⟨P, hP, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact LinearMap.ext fun x => hfix i (e.symm x i)
  · intro i j hij
    apply LinearMap.ext
    intro x
    change P i (P j x) = 0
    rw [hP j, hP i, hcoord]
    simp [Pi.single_eq_of_ne hij]
  · apply LinearMap.ext
    intro x
    simpa only [LinearMap.sum_apply, hP, Module.End.one_apply] using
      (he (e.symm x)).symm.trans (e.apply_symm_apply x)
  · intro i
    apply le_antisymm
    · rintro x ⟨y, rfl⟩
      exact (e.symm y i).property
    · intro x hx
      exact ⟨x, hfix i ⟨x, hx⟩⟩
  · intro g hg i
    have hnatural (x : M) : e.symm (g x) =
        fun j => ⟨g (e.symm x j), hg j (e.symm x j).property⟩ := by
      apply e.injective
      rw [e.apply_symm_apply, he, ← map_sum, ← he, e.apply_symm_apply]
    apply LinearMap.ext
    intro x
    change P i (g x) = g (P i x)
    rw [hP, hnatural, hP]

