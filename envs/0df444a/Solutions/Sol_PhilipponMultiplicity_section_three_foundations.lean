-- Prove2me | solution 1 for PhilipponMultiplicity.section_three_foundations
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-26T02:48:28.676338+00:00
-- url     : https://prove2.me/submissions/6903dbad-3b96-402f-86a7-52e72d7041de

import Theorems.Thm_PhilipponMultiplicity_multigraded_hilbert_polynomial_exists
import Theorems.Thm_PhilipponMultiplicity_multigraded_hilbert_polynomial_top_coefficients
import Theorems.Thm_PhilipponMultiplicity_Hilbert_hilbertPolynomial_zero_iff_trivial
import Theorems.Thm_PhilipponMultiplicity_Hilbert_relevantCore_krull_dimension
import Theorems.Thm_PhilipponMultiplicity_idealMixedDegree_integral
import Theorems.Thm_PhilipponMultiplicity_SectionThreeSupport_exists_primaryDecomposition
import Theorems.Thm_PhilipponMultiplicity_degreeCoefficientSum_eq
import Theorems.Thm_PhilipponMultiplicity_Hilbert_degreeValue_antitone_of_dimension_eq
import Theorems.Thm_PhilipponMultiplicity_SectionThreeSupport_PrimaryDecomposition_associatedPrimes_eq
import Theorems.Thm_PhilipponMultiplicity_SectionThreeSupport_dimensionSlice_mono
import Theorems.Thm_PhilipponMultiplicity_SectionThreeSupport_component_partition_primes
import Theorems.Thm_PhilipponMultiplicity_SectionThreeSupport_component_partition_cut
import Theorems.Thm_PhilipponMultiplicity_SectionThreeSupport_exists_embedded_regular
import Theorems.Thm_PhilipponMultiplicity_SectionThreeSupport_embedded_avoidance_on_open
import Definitions.Def_PhilipponMultiplicity_SectionThreeSupport
set_option autoImplicit false
open scoped BigOperators
open MvPolynomial PhilipponMultiplicity PhilipponMultiplicity.SectionThree
open PhilipponMultiplicity.SectionThreeSupport PhilipponMultiplicity.Hilbert

theorem solution
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (M : MultiProjectiveSpace K) :
    -- The actual Hilbert polynomial, its support, coefficients, and dimension.
    (∀ I : Ideal M.CoordinateRing, IsMultihomogeneousIdeal M I →
      (∃ P, Hilbert.IsHilbertPolynomial K M.factorCount M.ambientDimension I P) ∧
      (Hilbert.hilbertPolynomial K M.factorCount M.ambientDimension I = 0 ↔
        ¬ IsNontrivialIdeal M I) ∧
      (IsNontrivialIdeal M I →
        ringKrullDim (M.CoordinateRing ⧸ relevantRadicalCore M I) =
          ((idealDimension M I + M.factorCount : ℕ) : WithBot ℕ∞)) ∧
      (∀ α : M.FactorIndex → ℕ, ∃ n : ℕ, idealMixedDegree M I α = (n : ℚ)) ∧
      (∀ α : M.FactorIndex → ℕ, (∃ i, M.ambientDimension i < α i) →
        idealMixedDegree M I α = 0) ∧
      (∀ d : M.FactorIndex → ℕ, idealDegreeValue M I d = degreeCoefficientSum M I d) ∧
      Nonempty (PrimaryDecomposition M I)) ∧
    -- Equal-dimensional Hilbert-degree monotonicity following Lemma 3.2.
    (∀ I J : Ideal M.CoordinateRing,
      IsMultihomogeneousIdeal M I → IsMultihomogeneousIdeal M J →
      IsNontrivialIdeal M I → IsNontrivialIdeal M J → I ≤ J →
      idealDimension M I = idealDimension M J →
      ∀ d : M.FactorIndex → ℕ, (∀ i, 1 ≤ d i) →
        idealDegreeValue M J d ≤ idealDegreeValue M I d) ∧
    -- Associated primes of a genuine minimal primary decomposition.
    (∀ I : Ideal M.CoordinateRing, ∀ D : PrimaryDecomposition M I,
      associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I) =
        Set.range (fun i => (D.component i).radical)) ∧
    -- Fact A, using the actual canonical isolated primary components.
    (∀ J J' : Ideal M.CoordinateRing,
      IsMultihomogeneousIdeal M J → IsMultihomogeneousIdeal M J' →
      IsNontrivialIdeal M J → IsNontrivialIdeal M J' → J ≤ J' →
      ∀ b : ℕ, (dimensionAtLeast M J (b + 1)).radical =
          (dimensionAtLeast M J' (b + 1)).radical →
        dimensionSlice M J b ≤ dimensionSlice M J' b) ∧
    -- Facts B and C: the canonical partition of the isolated components.
    (∀ J I : Ideal M.CoordinateRing, J ≤ I →
      (∀ q ∈ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I),
        ∃ p ∈ J.minimalPrimes, p ≤ q) ∧
      (∀ p ∈ J.minimalPrimes,
        p ∉ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I) → ¬ I ≤ p) ∧
      (∀ P ∈ I,
        (J ⊔ Ideal.span {P}).radical =
          (discardedPart M J I ⊔ Ideal.span {P}).radical ⊓ (retainedPart M J I).radical ∧
        ∀ q ∈ J.minimalPrimes,
          q ∈ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I) →
          q ∈ (J ⊔ Ideal.span {P}).minimalPrimes)) ∧
    -- Fact D, slightly stronger: retain all isolated components, even irrelevant ones.
    (∀ I : Ideal M.CoordinateRing, ∀ D : PrimaryDecomposition M I,
      ∃ Q ∈ D.embeddedIntersection,
        IsRegular (Ideal.Quotient.mk D.isolatedIntersection Q)) ∧
    -- Fact E: embedded supports avoid the Cohen–Macaulay locus; prime avoidance.
    (∀ I : Ideal M.CoordinateRing, ∀ D : PrimaryDecomposition M I,
      ∀ U : MaximalOpenLocus M, IsLocallyCohenMacaulayOn M I U →
      (∀ i : Fin D.count, D.IsEmbedded i →
        ¬ Hilbert.MeetsOpen K M.factorCount M.ambientDimension (D.component i).radical U) ∧
      (∀ L : Ideal M.CoordinateRing,
        (∀ q ∈ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ L),
          Hilbert.MeetsOpen K M.factorCount M.ambientDimension q U) →
        (∀ i : Fin D.count, D.IsEmbedded i →
          ∀ q ∈ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ L),
            ¬ (D.component i).radical ≤ q) ∧
        ∃ Q ∈ D.embeddedIntersection, IsRegular (Ideal.Quotient.mk L Q))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro I hI
    refine ⟨multigraded_hilbert_polynomial_exists K M I hI,
      hilbertPolynomial_zero_iff_trivial M I hI,
      relevantCore_krull_dimension M I hI,
      idealMixedDegree_integral M I hI, ?_, degreeCoefficientSum_eq M I hI,
      exists_primaryDecomposition M I hI⟩
    intro α hα
    have hc := (multigraded_hilbert_polynomial_top_coefficients K M I hI).2
      (Finsupp.equivFunOnFinite.symm α) hα
    unfold idealMixedDegree
    split_ifs with hd
    · have he : (Finsupp.equivFunOnFinite.symm α).degree = idealDimension M I := by
        simpa only [Finsupp.degree_eq_sum, Finsupp.sum_fintype, Finsupp.coe_equivFunOnFinite_symm] using hd
      rw [coeff_homogeneousComponent, if_pos (show (Finsupp.equivFunOnFinite.symm α).degree =
        (hilbertPolynomial K M.factorCount M.ambientDimension I).totalDegree from he)] at hc
      rw [hc, zero_mul]
    · rfl
  · intro I J hI hJ _ _ hle hdim d _
    exact degreeValue_antitone_of_dimension_eq M I J hI hJ hle hdim d
  · intro I D
    exact PrimaryDecomposition.associatedPrimes_eq M I D
  · intro J J' hJ hJ' _ _ hle b heq
    exact dimensionSlice_mono M J J' hJ hJ' hle b heq
  · intro J I hle
    obtain ⟨h₁,h₂⟩ := component_partition_primes M J I hle
    exact ⟨h₁,h₂,fun P hP => component_partition_cut M J I hle P hP⟩
  · intro I D
    exact exists_embedded_regular M I D
  · intro I D U hU
    exact embedded_avoidance_on_open M I D U hU
