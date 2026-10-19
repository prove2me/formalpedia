-- Prove2me | solution 1 for PermanentFormulaLowerBound.TranscendenceBounds.trdeg_intermediateField_le_adjoin_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:11.481307+00:00
-- url     : https://prove2.me/submissions/fcc7b4bc-d71f-4bb9-9c3a-9a32bf4a4199

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentFormulaLowerBound_TranscendenceBounds_trdeg_intermediateField_adjoin_le_card

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
    (K : IntermediateField F E) (s : Finset E)
    (hK : K ≤ IntermediateField.adjoin F (s : Set E)) :
    Algebra.trdeg F K ≤ (s.card : Cardinal) := by
  calc
    Algebra.trdeg F K ≤
        Algebra.trdeg F (IntermediateField.adjoin F (s : Set E)) :=
      trdeg_le_of_injective (IntermediateField.inclusion hK)
        (IntermediateField.inclusion_injective hK)
    _ ≤ (s.card : Cardinal) :=
      trdeg_intermediateField_adjoin_le_card s
end PermanentFormulaLowerBound.TranscendenceBounds
