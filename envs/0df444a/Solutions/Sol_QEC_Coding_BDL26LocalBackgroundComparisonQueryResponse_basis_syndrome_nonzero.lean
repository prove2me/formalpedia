-- Prove2me | solution 1 for QEC.Coding.BDL26LocalBackgroundComparisonQueryResponse.basis_syndrome_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T14:36:13.030173+00:00
-- url     : https://prove2.me/submissions/d7e505d5-4df9-4e4f-b2ef-b1da12ab7c31

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_PairedHistoryQueryCone
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalBackgroundComparisonDepth
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalBackgroundComparisonQueryResponse
import Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_suffix_delta1
import Theorems.Thm_QEC_Coding_BDL26RZMap1CoordinateBridge_tannerCoboundary1_canonicalBasis_apply
attribute [local simp] QEC.Coding.BDL26RZMap1CoordinateBridge.tannerCoboundary1_canonicalBasis_apply



set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LocalBackgroundComparisonQueryResponse
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26RZMap1CoordinateBridge
open BDL26HistoryLogicalResidual (suffix_delta1)
open BDL26LocalBackgroundComparisonResponse BDL26PairedHistoryQueryCone
open MultiscaleDecoder
open scoped Classical BigOperators
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26LocalBackgroundComparisonQueryResponse
theorem _root_.solution (q : Q S n) :
    (SuffixData S n).family.coboundary1 (TopIndex n)
      (canonicalBasisWord (F:=BDL26Field) q) ≠ 0 := by
  let z := ((state S (n+2)).admissible.toTannerSquareAdmissible.qzRoot q).val
  have hi : (state S (n+2)).presentation.qz q z = true :=
    ((state S (n+2)).admissible.toTannerSquareAdmissible.qzRoot q).property
  intro hz
  have hv := congrFun hz z
  rw [suffix_delta1,tannerCoboundary1_canonicalBasis_apply,if_pos hi] at hv
  exact one_ne_zero hv
end QEC.Coding.BDL26LocalBackgroundComparisonQueryResponse
