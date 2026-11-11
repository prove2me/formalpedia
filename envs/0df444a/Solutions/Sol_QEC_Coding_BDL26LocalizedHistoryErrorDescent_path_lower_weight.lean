-- Prove2me | solution 1 for QEC.Coding.BDL26LocalizedHistoryErrorDescent.path_lower_weight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T18:21:40.711199+00:00
-- url     : https://prove2.me/submissions/ec80d21c-17f8-4e1d-bfff-6c8bb2c61ee1

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalXStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalizedHistoryErrorDescent
import Theorems.Thm_QEC_Coding_BDL26LocalizedHistoryErrorDescent_star_card
import Theorems.Thm_QEC_Coding_BDL26LocalizedHistoryErrorDescent_path_localized

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
theorem _root_.solution (a : LevelIndex n) (_below : a.val<n) :
    HammingWeight (path S n sigma tau top a).word ≤
        (star S n a (path S n sigma tau top a).center).card ∧
      (star S n a (path S n sigma tau top a).center).card ≤ 7 := by
  rw [HammingWeight_eq_card_hammingSupport]
  exact ⟨Finset.card_le_card (path_localized S n sigma tau top a),star_card S n a _⟩
end QEC.Coding.BDL26LocalizedHistoryErrorDescent
