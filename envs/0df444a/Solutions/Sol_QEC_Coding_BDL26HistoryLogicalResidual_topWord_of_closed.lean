-- Prove2me | solution 1 for QEC.Coding.BDL26HistoryLogicalResidual.topWord_of_closed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T19:17:21.781198+00:00
-- url     : https://prove2.me/submissions/8c43e530-f2a2-4d0e-93f2-7c11b995be33

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryLogicalResidual_Intervals
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryLogicalResidual_Words
import Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_perturbTop_of_closed
import Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_word_add_self
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistoryLogicalResidual
open MultiscaleDecoder BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open BDL26RZMap1CoordinateBridge
open scoped Classical
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26HistoryLogicalResidual
theorem _root_.solution (sigma : TopInput S n)
    (e : (SuffixData S n).family.Cochain1 (TopIndex n))
    (he : (SuffixData S n).family.coboundary1 (TopIndex n) e = 0) : topWord S n sigma e = e := by
  have hc : fullCorrection S n (perturbTop S n sigma e) = fullCorrection S n sigma :=
    congrArg (fullCorrection S n) (perturbTop_of_closed S n sigma e he)
  change e + fullCorrection S n sigma + fullCorrection S n (perturbTop S n sigma e) = e
  calc
    e + fullCorrection S n sigma + fullCorrection S n (perturbTop S n sigma e) =
        e + fullCorrection S n sigma + fullCorrection S n sigma :=
      congrArg (fun h : (SuffixData S n).family.Cochain1 (TopIndex n) =>
        e + fullCorrection S n sigma + h) hc
    _ = e + (fullCorrection S n sigma + fullCorrection S n sigma) := add_assoc e _ _
    _ = e := (congrArg (fun h : (SuffixData S n).family.Cochain1 (TopIndex n) => e+h)
      (word_add_self (fullCorrection S n sigma))).trans (add_zero e)
end QEC.Coding.BDL26HistoryLogicalResidual
