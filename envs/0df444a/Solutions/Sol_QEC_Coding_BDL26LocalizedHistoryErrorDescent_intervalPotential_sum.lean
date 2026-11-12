-- Prove2me | solution 1 for QEC.Coding.BDL26LocalizedHistoryErrorDescent.intervalPotential_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T23:36:49.749755+00:00
-- url     : https://prove2.me/submissions/cfe7569a-416e-4704-8c06-a488d95b7e72

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalXStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalizedHistoryErrorDescent

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LocalizedHistoryErrorDescent
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open scoped Classical BigOperators
variable (S : OddScale) (n : Nat) (sigma tau : TopInput S n)
variable (top : LocalizedWord S n sigma tau (TopIndex n))
namespace QEC.Coding.BDL26LocalizedHistoryErrorDescent
theorem _root_.solution (a b : LevelIndex n) :
    intervalPotential S n sigma tau top a b=
      ∑ i : StepIndex n, (if h : a.val< (i.succ).val ∧ (i.succ).val≤b.val then
        intervalMap0 (Data S n) i.succ b h.2 (edgePotential S n sigma tau top i) else 0) := rfl
end QEC.Coding.BDL26LocalizedHistoryErrorDescent
