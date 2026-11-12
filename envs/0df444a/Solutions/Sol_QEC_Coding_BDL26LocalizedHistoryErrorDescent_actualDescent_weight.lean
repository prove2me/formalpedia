-- Prove2me | solution 1 for QEC.Coding.BDL26LocalizedHistoryErrorDescent.actualDescent_weight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T23:40:11.453444+00:00
-- url     : https://prove2.me/submissions/9397e451-373f-4bb5-bd99-7f8bcfd8db7c

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalXStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalizedHistoryErrorDescent
import Theorems.Thm_QEC_Coding_BDL26LocalizedHistoryErrorDescent_path_lower_weight

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LocalizedHistoryErrorDescent
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open scoped Classical BigOperators
variable (S : OddScale) (n : Nat) (sigma tau : TopInput S n)
variable (top : LocalizedWord S n sigma tau (TopIndex n))
variable (e : (Data S n).family.Cochain1 (TopIndex n))
variable (x : (state S (n+2)).presentation.X) (he : hammingSupport e ⊆ star S n (TopIndex n) x)
namespace QEC.Coding.BDL26LocalizedHistoryErrorDescent
theorem _root_.solution (a : LevelIndex n) (ha : a.val<n) :
    HammingWeight (actualDescent S n sigma e x he a).word≤
        (star S n a (actualDescent S n sigma e x he a).center).card ∧
      (star S n a (actualDescent S n sigma e x he a).center).card≤7 :=
  path_lower_weight S n sigma (perturbTop S n sigma e) (initial S n sigma e x he) a ha
end QEC.Coding.BDL26LocalizedHistoryErrorDescent
