-- Prove2me | solution 1 for QEC.Coding.BDL26CanonicalHistoryMarks.entryAt_components
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T22:45:16.004931+00:00
-- url     : https://prove2.me/submissions/3f454fb3-b7f8-476b-b8ee-7adf29306848

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_HistoryWitness
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Snapshots
import Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_entryAt_step

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26CanonicalHistoryMarks
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks MultiscaleDecoder
open scoped Classical
variable (S : OddScale) (n : Nat)
variable (sigma : Input S n)
namespace QEC.Coding.BDL26CanonicalHistoryMarks
theorem _root_.solution (i : StepIndex n) :
    (entryAt S n sigma i.succ).localComponents =
      (outputAt S n sigma i).localComponents.map (fun f => ⟨i.succ, f⟩) := by
  rw [entryAt_step]
  rfl
end QEC.Coding.BDL26CanonicalHistoryMarks
