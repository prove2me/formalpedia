-- Prove2me | solution 1 for PhilipponMultiplicity.SectionThreeSupport.componentSum_regular_cut_le_of_equidimensional
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-27T00:59:32.088427+00:00
-- url     : https://prove2.me/submissions/b1e4da51-9247-4dce-b735-98c1a6179024

import Definitions.Def_PhilipponMultiplicity_SectionThreeSupport
import Theorems.Thm_PhilipponMultiplicity_Hilbert_relevant_hypersurface_component_dimension
import Theorems.Thm_PhilipponMultiplicity_Hilbert_minimalPrime_homogeneous
import Theorems.Thm_PhilipponMultiplicity_SectionThreeSupport_componentSum_regular_cut_le_of_dimensions

set_option autoImplicit false
open scoped BigOperators
open MvPolynomial PhilipponMultiplicity PhilipponMultiplicity.SectionThree
open PhilipponMultiplicity.SectionThreeSupport PhilipponMultiplicity.Hilbert
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.Hilbert
open SectionThree
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem notMem_minimalPrime_of_quotient_regular (I p : Ideal M.CoordinateRing)
    (hp : p ∈ I.minimalPrimes) (P : M.CoordinateRing)
    (hregular : IsRegular (Ideal.Quotient.mk I P)) : P ∉ p := by
  rw [Ideal.minimalPrimes_eq_comap] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  intro hP
  change Ideal.Quotient.mk I P ∈ q at hP
  exact (notMem_nonZeroDivisors_of_mem_mem_minimalPrimes hP hq)
    hregular.mem_nonZeroDivisors

/-- The geometric dimension statement extends from primes to homogeneous
ideals whose relevant minimal components all have the ideal's dimension. -/
theorem equidimensional_regular_cut_component_dimension (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I)
    (hdim : ∀ p ∈ I.minimalPrimes,
      IsRelevant K M.factorCount M.ambientDimension p →
      idealDimension M p = idealDimension M I)
    (P : M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (hP : M.IsHomogeneous P D) (hregular : IsRegular (Ideal.Quotient.mk I P))
    (q : Ideal M.CoordinateRing) (hq : q ∈ (I ⊔ Ideal.span {P}).minimalPrimes)
    (hqr : IsRelevant K M.factorCount M.ambientDimension q) :
    idealDimension M q + 1 = idealDimension M I := by
  let : q.IsPrime := hq.isPrime
  have hIq : I ≤ q := le_sup_left.trans hq.le
  obtain ⟨p, hp, hpq⟩ := Ideal.exists_minimalPrimes_le hIq
  have hpr : IsRelevant K M.factorCount M.ambientDimension p := fun h => hqr (h.trans hpq)
  have hq' : q ∈ (p ⊔ Ideal.span {P}).minimalPrimes := by
    refine ⟨⟨hq.isPrime, sup_le hpq (le_sup_right.trans hq.le)⟩, ?_⟩
    intro r hr hrq
    exact hq.2 ⟨hr.1, sup_le (hp.le.trans (le_sup_left.trans hr.2))
      (le_sup_right.trans hr.2)⟩ hrq
  have hd := relevant_hypersurface_component_dimension M p hp.isPrime
    (minimalPrime_homogeneous M I p hI hp) P D hP
    (notMem_minimalPrime_of_quotient_regular M I p hp P hregular) q hq' hqr
  rwa [hdim p hp hpr] at hd

end PhilipponMultiplicity.Hilbert

namespace PhilipponMultiplicity.SectionThreeSupport
open SectionThree
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

/-- The one-cut bound for equidimensional relevant support. The conclusion
has no hypothesis about the cut's component dimensions; those follow through
the explicitly imported geometric foundation sketch. -/
theorem componentSum_regular_cut_le_of_equidimensional (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I)
    (hdim : ∀ p ∈ I.minimalPrimes,
      Hilbert.IsRelevant K M.factorCount M.ambientDimension p →
      idealDimension M p = idealDimension M I)
    (P : M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (hP : M.IsHomogeneous P D) (hregular : IsRegular (Ideal.Quotient.mk I P))
    (U : MaximalOpenLocus M) :
    componentHilbertSum M (I ⊔ Ideal.span {P}) U D ≤ idealDegreeValue M I D := by
  apply componentSum_regular_cut_le_of_dimensions M I hI P D hP hregular
  exact fun q hq hqr => Hilbert.equidimensional_regular_cut_component_dimension
    M I hI hdim P D hP hregular q hq hqr

end PhilipponMultiplicity.SectionThreeSupport

theorem solution
    {K : Type*} [Field K] (M : MultiProjectiveSpace K)
(I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I)
    (hdim : ∀ p ∈ I.minimalPrimes,
      Hilbert.IsRelevant K M.factorCount M.ambientDimension p →
      idealDimension M p = idealDimension M I)
    (P : M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (hP : M.IsHomogeneous P D) (hregular : IsRegular (Ideal.Quotient.mk I P))
    (U : MaximalOpenLocus M) :
    componentHilbertSum M (I ⊔ Ideal.span {P}) U D ≤ idealDegreeValue M I D := by
  exact PhilipponMultiplicity.SectionThreeSupport.componentSum_regular_cut_le_of_equidimensional M I hI hdim P D hP hregular U
