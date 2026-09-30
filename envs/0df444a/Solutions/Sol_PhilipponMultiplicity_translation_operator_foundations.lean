-- Prove2me | solution 1 for PhilipponMultiplicity.translation_operator_foundations
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-27T17:49:54.920867+00:00
-- url     : https://prove2.me/submissions/d8cad822-5e75-4fa5-9b94-98a07e8f540b

import Theorems.Thm_PhilipponMultiplicity_translation_operator_algebra
import Theorems.Thm_PhilipponMultiplicity_retained_polynomial_operator_ideal_laws
import Theorems.Thm_PhilipponMultiplicity_differentialIdeal_vanishingIdeal
import Theorems.Thm_PhilipponMultiplicity_exists_uniformly_bounded_translation_atlas
import Theorems.Thm_PhilipponMultiplicity_retainedPolynomialOperatorIdeal_eq_differentialIdeal
import Definitions.Def_PhilipponMultiplicity_SectionFour
set_option autoImplicit false
open scoped BigOperators Topology
open PhilipponMultiplicity
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.MultiProjectiveSpace
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem blockWeight_apply (d : M.Variable →₀ ℕ) (i : M.FactorIndex) :
    (Finsupp.weight (Hilbert.blockWeight M.factorCount M.ambientDimension) d) i =
      ∑ j : Fin (M.ambientDimension i + 1), d ⟨i, j⟩ := by
  classical
  rw [Finsupp.weight_eq_sum, Fintype.sum_sigma]
  change (∑ b : M.FactorIndex,
    ∑ j : Fin (M.ambientDimension b + 1),
      d ⟨b, j⟩ • Hilbert.blockWeight M.factorCount M.ambientDimension ⟨b, j⟩) i = _
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Hilbert.blockWeight,
    Pi.single_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b hb hbi
    simp [Ne.symm hbi]
  · simp

theorem degreePiece_iff (P : M.CoordinateRing) (D : M.FactorIndex → ℕ) :
    P ∈ Hilbert.degreePiece K M.factorCount M.ambientDimension D ↔ M.IsHomogeneous P D := by
  change (∀ d, coeff d P ≠ 0 →
    Finsupp.weight (Hilbert.blockWeight M.factorCount M.ambientDimension) d = D) ↔ _
  simp only [← mem_support_iff]
  constructor
  · intro h d hd i
    exact (M.blockWeight_apply d i).symm.trans (congrFun (h d hd) i)
  · intro h d hd
    funext i
    rw [M.blockWeight_apply]
    exact h d hd i


end PhilipponMultiplicity.MultiProjectiveSpace

namespace PhilipponMultiplicity
private theorem completeSpace_of_isometric_ringEquiv
    {K F : Type*} [NontriviallyNormedField K] [NontriviallyNormedField F]
    [CompleteSpace F] (e : K ≃+* F) (he : Isometry e) : CompleteSpace K :=
  (he.isUniformInducing.completeSpace_congr e.surjective).mpr inferInstance

theorem IsPhilipponBaseField.completeSpace {K : Type*} [NontriviallyNormedField K]
    (hK : IsPhilipponBaseField K) : CompleteSpace K := by
  rcases hK with ⟨e, he⟩ | ⟨p, hp, h⟩
  · exact completeSpace_of_isometric_ringEquiv e he
  · letI : Fact p.Prime := ⟨hp⟩
    obtain ⟨e, he⟩ := h
    exact completeSpace_of_isometric_ringEquiv e he


end PhilipponMultiplicity

namespace PhilipponMultiplicity.OperatorSupport

theorem group_vanishingIdeal_multihomogeneous {K : Type*} [NontriviallyNormedField K]
    (G : EmbeddedGroupProduct K) : IsMultihomogeneousIdeal G.ambient (G.vanishingIdeal Set.univ) := by
  classical
  let M := G.ambient
  let w := Hilbert.blockWeight M.factorCount M.ambientDimension
  letI := MvPolynomial.weightedGradedAlgebra K w
  have hh : (G.vanishingIdeal Set.univ).IsHomogeneous (weightedHomogeneousSubmodule K w) := by
    apply Ideal.homogeneous_span
    intro P hP
    obtain ⟨D, hD⟩ := hP.1
    exact ⟨D, (M.degreePiece_iff P D).mpr hD⟩
  intro P hP d
  exact weightedHomogeneousComponent_mem_of_mem K w hh hP d

end PhilipponMultiplicity.OperatorSupport

end

theorem solution
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K) :
    (∃ c : EmbeddedCommutativeGroup K → ℕ, (∀ E, 1 ≤ c E) ∧
      ∀ (G : EmbeddedGroupProduct K) (A : AnalyticSubgroup G) (g : G.Point),
        ∃ atlas : TranslationAtlas A g, atlas.IsBoundedBy (fun i => c (G.factor i))) ∧
    (∀ (G : EmbeddedGroupProduct K) (A : AnalyticSubgroup G) (g : G.Point)
        (chart : TranslationChart A g) (order : ℕ)
        (directions : Fin order → Fin A.parameterDimension),
      (∀ (P Q : G.CoordinateRing) (a : K),
        polynomialOperator chart order directions (P + Q) =
          polynomialOperator chart order directions P + polynomialOperator chart order directions Q ∧
        polynomialOperator chart order directions (MvPolynomial.C a * P) =
          MvPolynomial.C a * polynomialOperator chart order directions P) ∧
      (∀ (P : G.CoordinateRing) (D : G.FactorIndex → ℕ),
        G.ambient.IsHomogeneous P D →
        G.ambient.IsHomogeneous (polynomialOperator chart order directions P)
          (fun i => chart.degree i * D i))) ∧
    (∀ (G : EmbeddedGroupProduct K) (A : AnalyticSubgroup G) (g : G.Point)
        (chart : TranslationChart A g) (directions : Fin 0 → Fin A.parameterDimension),
      ∃ f : G.CoordinateRing →ₐ[K] G.CoordinateRing,
        ∀ P, f P = polynomialOperator chart 0 directions P) ∧
    (∀ (G : EmbeddedGroupProduct K) (A : AnalyticSubgroup G) (g : G.Point)
        (atlas : TranslationAtlas A g) (T : ℕ)
        (I J : Ideal G.CoordinateRing),
      IsMultihomogeneousIdeal G.ambient I → IsMultihomogeneousIdeal G.ambient J →
      (retainedPolynomialOperatorIdeal atlas T I = differentialIdeal A g T I) ∧
      (I ≤ J → retainedPolynomialOperatorIdeal atlas T I ≤
        retainedPolynomialOperatorIdeal atlas T J) ∧
      (retainedPolynomialOperatorIdeal atlas T (I ⊔ J) =
        retainOnGroup G (retainedPolynomialOperatorIdeal atlas T I ⊔
          retainedPolynomialOperatorIdeal atlas T J))) ∧
    (∀ (G : EmbeddedGroupProduct K) (A : AnalyticSubgroup G) (g : G.Point)
        (atlas : TranslationAtlas A g) (T : ℕ),
      retainedPolynomialOperatorIdeal atlas T (G.vanishingIdeal Set.univ) =
        G.vanishingIdeal Set.univ) := by
  letI : CompleteSpace K := hK.completeSpace
  obtain ⟨hlinear, hzero⟩ := translation_operator_algebra K
  refine ⟨exists_uniformly_bounded_translation_atlas K hK, hlinear, hzero, ?_, ?_⟩
  · intro G A g atlas T I J hI hJ
    exact ⟨retainedPolynomialOperatorIdeal_eq_differentialIdeal K hK G A g atlas T I hI,
      retained_polynomial_operator_ideal_laws K G A g atlas T I J hI hJ⟩
  · intro G A g atlas T
    rw [retainedPolynomialOperatorIdeal_eq_differentialIdeal K hK G A g atlas T _
      (OperatorSupport.group_vanishingIdeal_multihomogeneous G)]
    exact differentialIdeal_vanishingIdeal K G A g T

