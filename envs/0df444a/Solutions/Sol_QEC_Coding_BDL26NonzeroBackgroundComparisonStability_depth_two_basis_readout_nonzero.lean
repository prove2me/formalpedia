-- Prove2me | solution 1 for QEC.Coding.BDL26NonzeroBackgroundComparisonStability.depth_two_basis_readout_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T14:26:35.303176+00:00
-- url     : https://prove2.me/submissions/6ae126e3-92a9-4720-8de0-d6e83d4b5248

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_AllDepthBottomComparisonStability
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NonzeroBackgroundComparisonStability
import Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_suffix_delta0
import Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_suffix_delta1
import Theorems.Thm_QEC_Coding_BDL26RZMap1CoordinateBridge_tannerCoboundary1_canonicalBasis_apply
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm
attribute [local simp] QEC.Coding.BDL26RZMap1CoordinateBridge.tannerCoboundary1_canonicalBasis_apply



set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26NonzeroBackgroundComparisonStability
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open BDL26HistoryLogicalResidual (suffix_delta0 suffix_delta1)
open BDL26RZMap1CoordinateBridge
open scoped Classical BigOperators
namespace QEC.Coding.BDL26NonzeroBackgroundComparisonStability
theorem _root_.solution (S : OddScale) (q : TopQ S 0) :
    BDL26AllDepthBottomComparisonStability.baseReadout S 0
      (perturbTop S 0 (zeroInput S 0) (canonicalBasisWord (F:=F) q))≠0 := by
  let e : TopWord S 0 := canonicalBasisWord (F:=F) q
  let z := ((state S 2).admissible.toTannerSquareAdmissible.qzRoot q).val
  have incident : (state S 2).presentation.qz q z=true :=
    ((state S 2).admissible.toTannerSquareAdmissible.qzRoot q).property
  have value : tannerCoboundary1 (state S 2).presentation e z=1 := by
    rw [tannerCoboundary1_canonicalBasis_apply,if_pos incident]
  have readout : BDL26AllDepthBottomComparisonStability.baseReadout S 0 (perturbTop S 0 (zeroInput S 0) e)=
      tannerCoboundary1 (state S 2).presentation e := by
    rw [depth_two_readout]
    change 0+(Data S 0).family.coboundary1 (TopIndex 0) e=_
    exact (zero_add ((Data S 0).family.coboundary1 (TopIndex 0) e)).trans
      (LinearMap.congr_fun (suffix_delta1 S 0 (TopIndex 0)) e)
  intro hz
  have scalar := congrFun (readout.symm.trans hz) z
  exact one_ne_zero (value.symm.trans scalar)
end QEC.Coding.BDL26NonzeroBackgroundComparisonStability
