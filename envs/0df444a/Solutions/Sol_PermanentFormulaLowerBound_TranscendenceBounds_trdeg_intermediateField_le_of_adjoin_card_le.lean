-- Prove2me | solution 1 for PermanentFormulaLowerBound.TranscendenceBounds.trdeg_intermediateField_le_of_adjoin_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:11.481307+00:00
-- url     : https://prove2.me/submissions/3b00fa71-8286-4f0e-9586-8511066d6afd

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentFormulaLowerBound_TranscendenceBounds_trdeg_intermediateField_le_adjoin_card

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
open PermanentFormulaLowerBound.TranscendenceBounds
namespace PermanentFormulaLowerBound.TranscendenceBounds
theorem _root_.solution
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (K : IntermediateField F E) (s : Finset E) {budget : ℕ}
    (hK : K ≤ IntermediateField.adjoin F (s : Set E))
    (hbudget : s.card ≤ budget) :
    Algebra.trdeg F K ≤ (budget : Cardinal) :=
  (trdeg_intermediateField_le_adjoin_card K s hK).trans
    (Nat.cast_le.mpr hbudget)
end PermanentFormulaLowerBound.TranscendenceBounds
