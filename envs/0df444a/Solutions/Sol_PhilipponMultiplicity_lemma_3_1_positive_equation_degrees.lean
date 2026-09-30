-- Prove2me | solution 1 for PhilipponMultiplicity.lemma_3_1_positive_equation_degrees
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-25T22:40:47.334329+00:00
-- url     : https://prove2.me/submissions/1c807c43-6c85-47a5-b6f4-a8005c4dd903

import Theorems.Thm_PhilipponMultiplicity_lemma_3_1_of_hilbert_data
import Theorems.Thm_PhilipponMultiplicity_multigraded_hilbert_polynomial_exists
import Theorems.Thm_PhilipponMultiplicity_multigraded_hilbert_polynomial_top_coefficients
import Definitions.Def_PhilipponMultiplicity_SectionThree
set_option autoImplicit false
open scoped BigOperators
open MvPolynomial PhilipponMultiplicity PhilipponMultiplicity.SectionThree
open PhilipponMultiplicity.Hilbert

theorem solution
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (M : MultiProjectiveSpace K)
    (I : Ideal M.CoordinateRing) (hI : IsMultihomogeneousIdeal M I)
    (hNontrivial : IsNontrivialIdeal M I) (ha : 0 < idealDimension M I)
    (D : M.FactorIndex → ℕ) (hD : ∀ i, 1 ≤ D i)
    (P : M.CoordinateRing) (hP : M.IsHomogeneous P D)
    (hRegular : IsRegular (Ideal.Quotient.mk I P)) :
    (∀ d : M.FactorIndex → ℕ, (∀ i, 1 ≤ d i) →
      idealDegreeValue M (I ⊔ Ideal.span {P}) d = hypersurfaceCoefficientSum M I D d) ∧
    idealDegreeValue M (I ⊔ Ideal.span {P}) D = idealDegreeValue M I D := by
  obtain ⟨hp, hb⟩ := PhilipponMultiplicity.multigraded_hilbert_polynomial_top_coefficients K M I hI
  exact PhilipponMultiplicity.lemma_3_1_of_hilbert_data K M I hI
    (PhilipponMultiplicity.multigraded_hilbert_polynomial_exists K M I hI)
    hp hb ha D hD P hP hRegular
#print axioms solution
