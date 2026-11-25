-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ComplexSets_PrimitiveLinearForm_exists_linear_primitive_67c803d2091d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:22:53.518561+00:00
-- url     : https://prove2.me/submissions/10d6be53-7b1b-434b-a296-543678aec779

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PrimitiveLinearForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
open Polynomial TensorProduct
noncomputable section
open GroundTheory.Heights₂.Heights.ComplexSets.PrimitiveLinearForm
variable (R B : Type*) [CommRing R] [CommRing B] [Algebra R B]
attribute [local instance] tensorRightAlgebra
namespace GroundTheory.Heights₂.Heights.ComplexSets.PrimitiveLinearForm
theorem _root_.solution {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] {n : ℕ} (ι : ℂ →+* K) (x : Fin n → L)
    (hx : ∀ φ ψ : L →ₐ[K] AlgebraicClosure K, (∀ j, φ (x j) = ψ (x j)) → φ = ψ) :
    ∃ c : Fin n → ℂ, IntermediateField.adjoin K {∑ j, algebraMap K L (ι (c j)) * x j} = ⊤ := by
  classical
  let A := AlgebraicClosure K
  let ι' : ℂ →+* A := (algebraMap K A).comp ι
  let p : (L →ₐ[K] A) × (L →ₐ[K] A) → Polynomial A := fun φψ =>
    ∑ j : Fin n, Polynomial.monomial (j : ℕ) (φψ.1 (x j) - φψ.2 (x j))
  have hp : ∀ φψ : (L →ₐ[K] A) × (L →ₐ[K] A), φψ.1 ≠ φψ.2 → p φψ ≠ 0 := by
    intro φψ hne h
    apply hne
    apply hx
    intro j
    have hc := congrArg (fun q => Polynomial.coeff q (j : ℕ)) h
    simp only [p, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Polynomial.coeff_zero] at hc
    rw [Finset.sum_eq_single j] at hc
    · simpa [sub_eq_zero] using hc
    · intro b _ hb; rw [if_neg]; exact fun h => hb (Fin.ext h)
    · simp
  have hev : ∀ φψ : (L →ₐ[K] A) × (L →ₐ[K] A), ∀ t : A,
      (p φψ).eval t = ∑ j : Fin n, (φψ.1 (x j) - φψ.2 (x j)) * t ^ (j : ℕ) := by
    intro φψ t
    simp only [p, Polynomial.eval_finsetSum, Polynomial.eval_monomial]
  let S : Finset A := (Finset.univ.filter (fun φψ : (L →ₐ[K] A) × (L →ₐ[K] A) => φψ.1 ≠ φψ.2)).biUnion
    (fun φψ => (p φψ).roots.toFinset)
  have hSf : {t : ℂ | ι' t ∈ S}.Finite :=
    (S.finite_toSet.preimage (ι'.injective.injOn))
  obtain ⟨t, ht⟩ := hSf.infinite_compl.nonempty
  refine ⟨fun j => t ^ (j : ℕ), ?_⟩
  have hA : ∀ y : L, ((minpoly K y).map (algebraMap K A)).Splits := fun y => IsAlgClosed.splits _
  rw [Field.primitive_element_iff_algHom_eq_of_eval' K A hA]
  intro φ ψ hφψ
  by_contra hne
  apply ht
  simp only [Set.mem_ofPred_eq, S, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨(φ, ψ), hne, ?_⟩
  rw [Multiset.mem_toFinset, Polynomial.mem_roots (hp (φ, ψ) hne), Polynomial.IsRoot, hev]
  have h1 : ∀ χ : L →ₐ[K] A, χ (∑ j : Fin n, algebraMap K L (ι (t ^ (j : ℕ))) * x j) =
      ∑ j : Fin n, ι' t ^ (j : ℕ) * χ (x j) := by
    intro χ
    simp [map_sum, map_mul, AlgHom.commutes, ι', map_pow]
  have h2 := congrArg id hφψ
  simp only [id] at h2
  rw [h1, h1] at h2
  rw [← sub_eq_zero] at h2
  rw [← h2, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring
end GroundTheory.Heights₂.Heights.ComplexSets.PrimitiveLinearForm
