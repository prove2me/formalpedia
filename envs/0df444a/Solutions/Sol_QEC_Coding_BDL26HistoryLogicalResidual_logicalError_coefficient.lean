-- Prove2me | solution 1 for QEC.Coding.BDL26HistoryLogicalResidual.logicalError_coefficient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T19:30:15.539367+00:00
-- url     : https://prove2.me/submissions/5a4ec900-8482-450a-8ee5-a16553a6b746

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryLogicalResidual_Words
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryLogicalResidual
import Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_logicalError_closed
import Theorems.Thm_QEC_Coding_BDL26FiniteCohomology_finiteH1Equiv_symm_scalar
import Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_topWord_of_closed
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistoryLogicalResidual
open MultiscaleDecoder BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RZMap1CoordinateBridge
open scoped Classical
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26HistoryLogicalResidual
theorem _root_.solution (sigma : TopInput S n) :
    topCoefficient S n sigma (logicalError S n) = 1 := by
  have hw : topCocycle S n sigma (logicalError S n) = FC.generator S (n+2) 1 := by
    apply Subtype.ext
    exact topWord_of_closed S n sigma (logicalError S n) (logicalError_closed S n)
  unfold topCoefficient
  rw [hw]
  have hg : (FC.finiteH1Equiv S (n+2)).symm 1 =
      FC.classOf S (n+2) (FC.generator S (n+2) 1) :=
    BDL26FiniteCohomology.finiteH1Equiv_symm_scalar S (n+2) 1
  exact (congrArg (FC.finiteH1Equiv S (n+2)) hg).symm.trans
    ((FC.finiteH1Equiv S (n+2)).apply_symm_apply 1)
end QEC.Coding.BDL26HistoryLogicalResidual
