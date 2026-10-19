-- Prove2me | solution 1 for PermanentFormulaLowerBound.RationalFormula.rational_skeleton_trdeg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:12.090475+00:00
-- url     : https://prove2.me/submissions/5e5b7479-ef87-49f7-9e42-f7ededb5e19d

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentFormulaLowerBound_TranscendenceBounds_trdeg_intermediateField_le_of_adjoin_card_le
import Theorems.Thm_PermanentFormulaLowerBound_exists_polynomial_of_mem_coefficientRationalField
import Theorems.Thm_PermanentFormulaLowerBound_RationalFormula_rational_skeleton

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
open PermanentFormulaLowerBound.RationalFormula
noncomputable section
variable {Y Z F : Type*}
namespace PermanentFormulaLowerBound.RationalFormula
theorem _root_.solution [Field F]
    (f : RationalFormula (Y ⊕ Z) F) (hvalid : Valid f)
    (hmarked : 0 < yLeafCount f) (p : MvPolynomial (Y ⊕ Z) F)
    (houtput : eval f =
      algebraMap (MvPolynomial (Y ⊕ Z) F)
        (FractionRing (MvPolynomial (Y ⊕ Z) F)) p) :
    coefficientTranscendenceDegree p ≤
      ((6 * yLeafCount f - 3 : ℕ) : Cardinal) := by
  obtain ⟨s, hcard, hmem⟩ := rational_skeleton f hvalid hmarked
  let E : Type _ := rationalCoefficientField Z F
  let pY : MvPolynomial Y E :=
    MvPolynomial.map (algebraMap (MvPolynomial Z F) E)
      (MvPolynomial.sumAlgEquiv F Y Z p)
  have hsplit :
      splitEval f =
        algebraMap (MvPolynomial Y E)
          (FractionRing (MvPolynomial Y E)) pY := by
    rw [splitEval, houtput, splitFractionHom_algebraMap]
    rfl
  have hfields :
      rationalSkeletonField (Y := Y) s =
        coefficientRationalField (F := F) (Y := Y) s := by
    simp [rationalSkeletonField, coefficientRationalField,
      splitCoefficientHom_eq_algebraMap]
  have hpY :
      algebraMap (MvPolynomial Y E)
        (FractionRing (MvPolynomial Y E)) pY ∈
          coefficientRationalField (F := F) (Y := Y) s := by
    rw [← hsplit, ← hfields]
    exact hmem
  obtain ⟨g, hg⟩ :=
    exists_polynomial_of_mem_coefficientRationalField
      (F := F) (Y := Y) s pY hpY
  have hfield :
      coefficientField p ≤ IntermediateField.adjoin F (s : Set E) := by
    apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨α, rfl⟩
    change
      algebraMap (MvPolynomial Z F) E (coefficientPolynomial p α) ∈
        IntermediateField.adjoin F (s : Set E)
    have hcoeff :
        algebraMap (IntermediateField.adjoin F (s : Set E)) E
            (MvPolynomial.coeff α g) =
          algebraMap (MvPolynomial Z F) E
            (coefficientPolynomial p α) := by
      simpa [pY, MvPolynomial.coeff_map, coefficientPolynomial]
        using congrArg (MvPolynomial.coeff α) hg
    rw [← hcoeff]
    exact (MvPolynomial.coeff α g).property
  exact
    TranscendenceBounds.trdeg_intermediateField_le_of_adjoin_card_le
      (coefficientField p) s hfield hcard
end PermanentFormulaLowerBound.RationalFormula
