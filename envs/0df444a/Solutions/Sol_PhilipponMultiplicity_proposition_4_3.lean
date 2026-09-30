-- Prove2me | solution 1 for PhilipponMultiplicity.proposition_4_3
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-28T11:18:13.092512+00:00
-- url     : https://prove2.me/submissions/357bc2e8-deba-4271-b3c4-562fb429a5a6

import Theorems.Thm_PhilipponMultiplicity_retainedPolynomialOperatorIdeal_eq_differentialIdeal
import Theorems.Thm_PhilipponMultiplicity_iterated_jet_sections_eq_differentialIdeal
import Theorems.Thm_PhilipponMultiplicity_differentialIdeal_eq_iterated_jet_sections
import Definitions.Def_PhilipponMultiplicity_IteratedJets
set_option autoImplicit false
open scoped BigOperators Topology
open PhilipponMultiplicity
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter MvPolynomial
noncomputable section

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

namespace PhilipponMultiplicity.OperatorSupport
variable {K : Type*} [Field K]

theorem homogeneous_span (M : MultiProjectiveSpace K) (S : Set M.CoordinateRing)
    (hS : ∀ P ∈ S, ∃ D, M.IsHomogeneous P D) :
    IsMultihomogeneousIdeal M (Ideal.span S) := by
  classical
  let w := Hilbert.blockWeight M.factorCount M.ambientDimension
  letI := weightedGradedAlgebra K w
  have hh : (Ideal.span S).IsHomogeneous (weightedHomogeneousSubmodule K w) := by
    apply Ideal.homogeneous_span
    intro P hP
    obtain ⟨D,hD⟩ := hS P hP
    exact ⟨D,(M.degreePiece_iff P D).mpr hD⟩
  intro P hP D
  exact weightedHomogeneousComponent_mem_of_mem K w hh hP D

end PhilipponMultiplicity.OperatorSupport

end

theorem solution
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) (A : AnalyticSubgroup G)
    (g g' : G.Point) (k k' : ℕ) (I : Ideal G.CoordinateRing)
    (hI : IsMultihomogeneousIdeal G.ambient I)
    (atlas atlas' : TranslationAtlas A g) :
    (retainedPolynomialOperatorIdeal atlas k I =
      retainedPolynomialOperatorIdeal atlas' k I) ∧
    (∀ other : TranslationAtlas A g', ∀ combined : TranslationAtlas A (g + g'),
      retainedPolynomialOperatorIdeal atlas k
        (retainedPolynomialOperatorIdeal other k' I) =
      retainedPolynomialOperatorIdeal combined (k + k') I) := by
  letI : CompleteSpace K := hK.completeSpace
  have hd : IsMultihomogeneousIdeal G.ambient (differentialIdeal A g' k' I) := by
    apply OperatorSupport.homogeneous_span
    intro P hP
    exact hP.1
  refine ⟨(retainedPolynomialOperatorIdeal_eq_differentialIdeal K hK G A g atlas k I hI).trans
    (retainedPolynomialOperatorIdeal_eq_differentialIdeal K hK G A g atlas' k I hI).symm,?_⟩
  intro other combined
  rw [retainedPolynomialOperatorIdeal_eq_differentialIdeal K hK G A g' other k' I hI]
  exact (retainedPolynomialOperatorIdeal_eq_differentialIdeal K hK G A g atlas k _ hd).trans
    ((differentialIdeal_eq_iterated_jet_sections K hK G A g g' k k' I hI).trans
      ((iterated_jet_sections_eq_differentialIdeal K G A g g' k k' I).trans
        (retainedPolynomialOperatorIdeal_eq_differentialIdeal K hK G A (g+g') combined
          (k+k') I hI).symm))

