-- Prove2me | solution 1 for QEC.Coding.BDL26LocalizedHistoryErrorDescent.down_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T18:00:58.934197+00:00
-- url     : https://prove2.me/submissions/90905393-d4e3-4edb-89fe-4cb670425df7

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
namespace QEC.Coding.BDL26LocalizedHistoryErrorDescent
theorem _root_.solution (b : Nat) (hb : b ≤ n)
    (u : LocalizedWord S n sigma tau ⟨b,Nat.lt_succ_of_le hb⟩) :
    down S n sigma tau b hb u ⟨b,Nat.lt_succ_of_le hb⟩ (Nat.le_refl _)=u := by
  cases b with
  | zero => rw [down]; rfl
  | succ b => rw [down]; exact dif_pos rfl
end QEC.Coding.BDL26LocalizedHistoryErrorDescent
