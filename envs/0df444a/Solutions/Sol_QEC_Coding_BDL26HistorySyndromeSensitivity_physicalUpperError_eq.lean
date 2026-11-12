-- Prove2me | solution 1 for QEC.Coding.BDL26HistorySyndromeSensitivity.physicalUpperError_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T23:05:57.610199+00:00
-- url     : https://prove2.me/submissions/9a7456bc-9f27-4c79-a84d-eb81a2a77a37

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Snapshots
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXErrorPullback
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZErrorPullback
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Preimages

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistorySyndromeSensitivity
open BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open MultiscaleDecoder
open scoped Classical
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26HistorySyndromeSensitivity
theorem _root_.solution (i : StepIndex n)
    (e : (SuffixData S n).family.Cochain1 i.succ) :
    physicalUpperError S n i e = e := rfl
end QEC.Coding.BDL26HistorySyndromeSensitivity
