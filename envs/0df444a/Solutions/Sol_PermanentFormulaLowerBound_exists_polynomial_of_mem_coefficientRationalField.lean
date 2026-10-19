-- Prove2me | solution 1 for PermanentFormulaLowerBound.exists_polynomial_of_mem_coefficientRationalField
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:12.090475+00:00
-- url     : https://prove2.me/submissions/755e030f-48d5-4f30-946c-207496e1fe5d

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentFormulaLowerBound_polynomial_intersection_of_mul
import Theorems.Thm_PermanentFormulaLowerBound_coefficientRationalField_le_fractionRange

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
noncomputable section
variable {F E Y : Type*} [Field F] [Field E] [Algebra F E]
namespace PermanentFormulaLowerBound
theorem _root_.solution
    (s : Finset E) (p : MvPolynomial Y E)
    (hp : algebraMap (MvPolynomial Y E) (FractionRing (MvPolynomial Y E)) p ∈
      coefficientRationalField (F := F) (Y := Y) s) :
    ∃ g : MvPolynomial Y (IntermediateField.adjoin F (s : Set E)),
      MvPolynomial.map
        (algebraMap (IntermediateField.adjoin F (s : Set E)) E) g = p := by
  let K : IntermediateField F E := IntermediateField.adjoin F (s : Set E)
  have hfield :
      algebraMap (MvPolynomial Y E) (FractionRing (MvPolynomial Y E)) p ∈
        (coefficientFractionEmbedding (Y := Y) K).fieldRange :=
    coefficientRationalField_le_fractionRange s hp
  obtain ⟨r, hr⟩ := AlgHom.mem_fieldRange.mp hfield
  obtain ⟨a, b, hb, hab⟩ :=
    IsFractionRing.div_surjective (MvPolynomial Y K) r
  have hbzero : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbembed : coefficientPolynomialEmbedding (Y := Y) K b ≠ 0 := by
    intro hzero
    apply hbzero
    apply coefficientPolynomialEmbedding_injective (Y := Y) K
    simpa using hzero
  have hrat :
      coefficientPolynomialEmbedding (Y := Y) K a /
        coefficientPolynomialEmbedding (Y := Y) K b =
          algebraMap (MvPolynomial Y E) (FractionRing (MvPolynomial Y E)) p := by
    rw [← hab, map_div₀, coefficientFractionEmbedding_algebraMap,
      coefficientFractionEmbedding_algebraMap] at hr
    exact hr
  have hcrossFraction :
      coefficientPolynomialEmbedding (Y := Y) K b *
        algebraMap (MvPolynomial Y E) (FractionRing (MvPolynomial Y E)) p =
          coefficientPolynomialEmbedding (Y := Y) K a := by
    have hcross := (div_eq_iff hbembed).mp hrat
    simpa [mul_comm] using hcross.symm
  have hcross :
      MvPolynomial.map (algebraMap K E) b * p =
        MvPolynomial.map (algebraMap K E) a := by
    have hval : K.val.toRingHom = algebraMap K E := rfl
    rw [← hval]
    apply IsFractionRing.injective (MvPolynomial Y E)
      (FractionRing (MvPolynomial Y E))
    simpa [coefficientPolynomialEmbedding, map_mul] using hcrossFraction
  exact polynomial_intersection_of_mul p a b hbzero hcross
end PermanentFormulaLowerBound
