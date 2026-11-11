-- Prove2me | solution 1 for QEC.Coding.BDL26LocalizedHistoryErrorDescent.down_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T18:00:17.259939+00:00
-- url     : https://prove2.me/submissions/672359e7-7d0b-4460-bf32-ab62549c5dec

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
theorem _root_.solution (b : Nat) (hb : b+1 ≤ n)
    (u : LocalizedWord S n sigma tau ⟨b+1,Nat.lt_succ_of_le hb⟩)
    (a : LevelIndex n) (ha : a.val ≤ b) :
    down S n sigma tau (b+1) hb u a (by omega)=
      down S n sigma tau b (by omega) (step S n sigma tau ⟨b,by omega⟩ u).lower a ha := by
  rw [down]
  exact dif_neg (by omega)
end QEC.Coding.BDL26LocalizedHistoryErrorDescent
