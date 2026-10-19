-- Prove2me | solution 1 for PermanentFormulaLowerBound.Formula.formula_skeleton
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:13.22648+00:00
-- url     : https://prove2.me/submissions/7b506180-7b15-40ef-aa66-66d16d97791d

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentFormulaLowerBound_TranscendenceBounds_trdeg_intermediateField_le_of_adjoin_card_le
import Theorems.Thm_PermanentFormulaLowerBound_Formula_formula_skeleton_generators

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
open PermanentFormulaLowerBound.Formula
variable {Y : Type u} {Z : Type v} {F : Type w}
variable [Field F]
namespace PermanentFormulaLowerBound.Formula
theorem _root_.solution
    (f : Formula (Y ⊕ Z) F) (hmarked : 0 < yLeafCount f) :
    coefficientTranscendenceDegree (eval f) ≤
      ((4 * yLeafCount f - 2 : ℕ) : Cardinal) := by
  obtain ⟨s, hcard, hcoeff⟩ := formula_skeleton_generators f hmarked
  have hfield :
      coefficientField (eval f) ≤
        IntermediateField.adjoin F
          (s : Set (FractionRing (MvPolynomial Z F))) := by
    apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨α, rfl⟩
    exact hcoeff α
  exact
    TranscendenceBounds.trdeg_intermediateField_le_of_adjoin_card_le
      (coefficientField (eval f)) s hfield hcard
end PermanentFormulaLowerBound.Formula
