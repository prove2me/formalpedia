-- Prove2me | solution 1 for QEC.Coding.BDL26CanonicalHistoryMarks.inputAt_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T07:46:58.226882+00:00
-- url     : https://prove2.me/submissions/3c3a85bb-13e8-4711-8a9f-205f27278a97

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
theorem _root_.solution (i : StepIndex n) (O : AssemblyStepOutput (Data S n) i)
    (he : CorrectionHistoryEntry.step i O ∈ actualHistory S n sigma) :
    inputAt S n sigma i.succ = O.input := by
  have hh : HEq (entryAt S n sigma i.succ).inputSyndrome.2 O.input := by
    rw [entryAt_eq S n sigma i.succ (.step i O) he rfl]
    rfl
  exact eq_of_heq (rec_heq_of_heq (entryAt_spec S n sigma i.succ).2 hh)
end QEC.Coding.BDL26CanonicalHistoryMarks
