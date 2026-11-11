-- Prove2me | solution 1 for QEC.Coding.BDL26CanonicalHistoryMarks.inputAt_base
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T07:47:09.0262+00:00
-- url     : https://prove2.me/submissions/93dd020d-5f9c-44b7-8fc0-10c7221233c6

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_HistoryWitness
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Snapshots
import Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_entryAt_eq

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26CanonicalHistoryMarks
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks MultiscaleDecoder
open scoped Classical
variable (S : OddScale) (n : Nat)
variable (sigma : Input S n)
namespace QEC.Coding.BDL26CanonicalHistoryMarks
theorem _root_.solution (B : RecursiveBaseLevelCorrection (Data S n))
    (he : CorrectionHistoryEntry.base B ∈ actualHistory S n sigma) :
    inputAt S n sigma 0 = B.input := by
  have hh : HEq (entryAt S n sigma 0).inputSyndrome.2 B.input := by
    rw [entryAt_eq S n sigma 0 (.base B) he rfl]
    rfl
  exact eq_of_heq (rec_heq_of_heq (entryAt_spec S n sigma 0).2 hh)
end QEC.Coding.BDL26CanonicalHistoryMarks
