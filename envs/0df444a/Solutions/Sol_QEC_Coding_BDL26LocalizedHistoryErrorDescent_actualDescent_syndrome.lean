-- Prove2me | solution 1 for QEC.Coding.BDL26LocalizedHistoryErrorDescent.actualDescent_syndrome
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T18:15:55.970676+00:00
-- url     : https://prove2.me/submissions/6b0596fa-376e-476a-aa52-1f80a186defe

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalXStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalizedHistoryErrorDescent
import Theorems.Thm_QEC_Coding_BDL26LocalizedHistoryErrorDescent_path_syndrome

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
theorem _root_.solution (a : LevelIndex n) :
    (Data S n).family.coboundary1 a (actualDescent S n sigma e x he a).word=
      (actualInputs S n sigma a).val+(actualInputs S n (perturbTop S n sigma e) a).val :=
  path_syndrome S n sigma (perturbTop S n sigma e) (initial S n sigma e x he) a
end QEC.Coding.BDL26LocalizedHistoryErrorDescent
