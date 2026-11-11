-- Prove2me | solution 1 for QEC.Coding.BDL26CanonicalHistoryMarks.physicalMarks_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T06:19:06.80344+00:00
-- url     : https://prove2.me/submissions/75654ceb-df91-4087-9efc-3a7522e1520c

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Snapshots
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_PhysicalMarks

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26CanonicalHistoryMarks
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26ReplacementSupport MultiscaleDecoder
open scoped Classical BigOperators
variable (S : OddScale) (n : Nat) (sigma : Input S n)
namespace QEC.Coding.BDL26CanonicalHistoryMarks
theorem _root_.solution (i : StepIndex n) :
    physicalMarks S n sigma i.succ = aboveMarks S n sigma i := rfl
end QEC.Coding.BDL26CanonicalHistoryMarks
