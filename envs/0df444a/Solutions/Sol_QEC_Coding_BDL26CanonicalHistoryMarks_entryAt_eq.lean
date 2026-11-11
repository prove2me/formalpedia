-- Prove2me | solution 1 for QEC.Coding.BDL26CanonicalHistoryMarks.entryAt_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T06:58:59.300214+00:00
-- url     : https://prove2.me/submissions/382dc8f8-bc74-49eb-90c7-614803a33520

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_HistoryWitness
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Snapshots

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26CanonicalHistoryMarks
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks MultiscaleDecoder
open scoped Classical
variable (S : OddScale) (n : Nat)
variable (sigma : Input S n)
namespace QEC.Coding.BDL26CanonicalHistoryMarks
theorem _root_.solution (i : LevelIndex n) (e : CorrectionHistoryEntry (Data S n))
    (he : e ∈ actualHistory S n sigma) (hi : e.inputSyndrome.1 = i) :
    entryAt S n sigma i = e :=
  (entry_existsUnique S n sigma i).unique (entryAt_spec S n sigma i) ⟨he, hi⟩
end QEC.Coding.BDL26CanonicalHistoryMarks
