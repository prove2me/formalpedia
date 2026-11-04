-- Prove2me | solution 1 for ThreeSum.LightSharedReportingPair.program_meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T18:52:05.717666+00:00
-- url     : https://prove2.me/submissions/e221b11f-4147-4a97-9dba-a371b164c0ca

import Definitions.Def_Submission_ThreeSum_LightSharedReportingLevels
import Definitions.Def_Submission_ThreeSum_SharedReportingBankSourceBounds
import Definitions.Def_Submission_ThreeSum_LightSharedReportingPair
import Theorems.Thm_Light_Ends_append
import Theorems.Thm_Light_Exec_append
import Theorems.Thm_Light_Meets_append
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_SolvesN_append
import Theorems.Thm_Light_Solves_append
import Theorems.Thm_ThreeSumApsp_AbsLe_append
import Theorems.Thm_ThreeSum_BandRawA_Stored_append
import Theorems.Thm_ThreeSum_LightBandEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightBandLookup_program_meets
import Theorems.Thm_ThreeSum_LightBlockBoxes_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_427f455cbe093cd3
import Theorems.Thm_ThreeSum_LightBlockChildren_program_meets
import Theorems.Thm_ThreeSum_LightBlockCoefficients_program_meets
import Theorems.Thm_ThreeSum_LightBlockQuery_program_meets
import Theorems.Thm_ThreeSum_LightBlockSourceHashes_program_meets
import Theorems.Thm_ThreeSum_LightBooleanDot_program_meets
import Theorems.Thm_ThreeSum_LightBoxStages_program_meets
import Theorems.Thm_ThreeSum_LightBoxSum_program_meets
import Theorems.Thm_ThreeSum_LightCanonicalBoxSum_program_meets
import Theorems.Thm_ThreeSum_LightCapacity_program_meets
import Theorems.Thm_ThreeSum_LightCoverGreedy_program_meets
import Theorems.Thm_ThreeSum_LightCoverScores_program_meets
import Theorems.Thm_ThreeSum_LightCoverSelect_program_meets
import Theorems.Thm_ThreeSum_LightCoverUpdate_program_meets
import Theorems.Thm_ThreeSum_LightCyclic_program_meets
import Theorems.Thm_ThreeSum_LightDownsetAddress_program_meets
import Theorems.Thm_ThreeSum_LightDownsetEnumerationSetup_program_meets
import Theorems.Thm_ThreeSum_LightDownsetEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightDownsetSize_program_meets
import Theorems.Thm_ThreeSum_LightExplicitSum_program_meets
import Theorems.Thm_ThreeSum_LightKaratsuba_program_meets
import Theorems.Thm_ThreeSum_LightLeafSum_program_meets
import Theorems.Thm_ThreeSum_LightLocalCoverSchedule_program_meets
import Theorems.Thm_ThreeSum_LightLookupSum_program_meets
import Theorems.Thm_ThreeSum_LightMaskBits_program_meets
import Theorems.Thm_ThreeSum_LightMaskErase_program_meets
import Theorems.Thm_ThreeSum_LightMaskHashes_program_meets
import Theorems.Thm_ThreeSum_LightMaskMinimum_program_meets
import Theorems.Thm_ThreeSum_LightMaskUnion_program_meets
import Theorems.Thm_ThreeSum_LightModuloCounts_program_meets
import Theorems.Thm_ThreeSum_LightOneHot_program_meets
import Theorems.Thm_ThreeSum_LightOutputDecodeDigits_program_meets
import Theorems.Thm_ThreeSum_LightOutputDecodeDivide_program_meets
import Theorems.Thm_ThreeSum_LightPairFlags_program_meets
import Theorems.Thm_ThreeSum_LightPrimeChain_program_meets
import Theorems.Thm_ThreeSum_LightPrimeMinimum_program_meets
import Theorems.Thm_ThreeSum_LightQueryBox_program_meets
import Theorems.Thm_ThreeSum_LightQueryEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightQueryWeights_program_meets
import Theorems.Thm_ThreeSum_LightRadixDigit_program_meets
import Theorems.Thm_ThreeSum_LightRadixKeys_program_meets
import Theorems.Thm_ThreeSum_LightRadixRows_program_meets
import Theorems.Thm_ThreeSum_LightReportingAffine_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_a2917ec7b7f9f23f
import Definitions.Def_WeightedCache3SUM_Alias_fc697fae61d94ff7
import Definitions.Def_WeightedCache3SUM_Alias_bb907f0b533f0452
import Definitions.Def_WeightedCache3SUM_Alias_fb2417efddae0cb5
import Definitions.Def_WeightedCache3SUM_Alias_7f1c96094f5b1c13
import Definitions.Def_WeightedCache3SUM_Alias_00b35c3259394183
import Theorems.Thm_ThreeSum_LightReportingFilter_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_0d2857ef7f97fcc6
import Definitions.Def_WeightedCache3SUM_Alias_781f7abf8592a079
import Theorems.Thm_ThreeSum_LightReportingGather_program_meets
import Theorems.Thm_ThreeSum_LightReportingPackKeys_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_8a2cd73670b38080
import Definitions.Def_WeightedCache3SUM_Alias_bfa505cca5c6af3f
import Definitions.Def_WeightedCache3SUM_Alias_9e2aececf85d8818
import Definitions.Def_WeightedCache3SUM_Alias_f4a3749c14d0f5f9
import Definitions.Def_WeightedCache3SUM_Alias_a2387e9e7b890e99
import Definitions.Def_WeightedCache3SUM_Alias_a02564c7d1f1443e
import Theorems.Thm_ThreeSum_LightReportingSuffixBoxes_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_1d08961f6f3268cd
import Definitions.Def_WeightedCache3SUM_Alias_b15542bf609bcf98
import Definitions.Def_WeightedCache3SUM_Alias_362a3b2d8940306a
import Definitions.Def_WeightedCache3SUM_Alias_40e937d67ef507b4
import Definitions.Def_WeightedCache3SUM_Alias_dfc7d85d435022ae
import Definitions.Def_WeightedCache3SUM_Alias_c19df7a51d8d0351
import Theorems.Thm_ThreeSum_LightResidueHistogram_program_meets
import Theorems.Thm_ThreeSum_LightScaleArray_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_9ec307913a0c2e1a
import Definitions.Def_WeightedCache3SUM_Alias_70e2e63cbf342643
import Definitions.Def_WeightedCache3SUM_Alias_805a48d522fdb6f4
import Theorems.Thm_ThreeSum_LightSign_program_meets
import Theorems.Thm_ThreeSum_LightSignedBoxSetup_program_meets
import Theorems.Thm_ThreeSum_LightSignedLeafGeneral_program_meets
import Theorems.Thm_ThreeSum_LightSignedLeafTable_program_meets
import Theorems.Thm_ThreeSum_LightSignedLeaf_program_meets
import Theorems.Thm_ThreeSum_LightSmallDivide_program_meets
import Theorems.Thm_ThreeSum_LightSourceBuild_program_meets
import Theorems.Thm_ThreeSum_LightSourceGather_program_meets
import Theorems.Thm_ThreeSum_LightSourceHistogram_program_meets
import Theorems.Thm_ThreeSum_LightSourceOccurrenceArray_program_meets
import Theorems.Thm_ThreeSum_LightSourceResidues_program_meets
import Theorems.Thm_ThreeSum_LightSparseQuery_program_meets
import Theorems.Thm_ThreeSum_LightStageLookup_program_meets
import Theorems.Thm_ThreeSum_LightSubsetEnumerationSetup_program_meets
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightSubsetSetup_program_meets
import Theorems.Thm_ThreeSum_LightSwitchDepth_program_meets
import Theorems.Thm_ThreeSum_LightSwitch_program_meets
import Theorems.Thm_ThreeSum_LightWeightDecode_program_meets
import Theorems.Thm_ThreeSum_LightWeightRow_program_meets
import Theorems.Thm_ThreeSum_LightWeightedEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightWeightedScore_program_meets
import Theorems.Thm_ThreeSum_LightZetaCell_program_meets
import Theorems.Thm_ThreeSum_LightZetaPass_program_meets
import Theorems.Thm_ThreeSum_LightZetaStages_program_meets
import Theorems.Thm_ThreeSum_ReportingHostPairSegments_program_meets
import Theorems.Thm_ThreeSum_SharedReportingBankLevels_Built_append
import Theorems.Thm_ThreeSum_SharedReportingBankSources_left_abs_le
import Theorems.Thm_ThreeSum_SharedReportingBankSources_right_abs_le
import Definitions.Def_WeightedCache3SUM_Alias_63f976d8c876ac39
import Theorems.Thm_ThreeSum_SharedReportingBankSources_source_pair
set_option autoImplicit false
open ThreeSum ThreeSum.LightSharedReportingPair
open Light GlobalEncoding BlockIndexedQuery BlockSourceOccurrenceOrder
open SharedReportingBankLayout SharedReportingBankLevels SharedReportingBankSources
set_option maxHeartbeats 2400000
set_option maxRecDepth 11000
namespace ThreeSum.LightSharedReportingPair
theorem _root_.solution {lim : Limits} {μ : ℕ → ℤ} {fB fC : ℕ → ℤ} {header NB NC g h J occ s i j K record base d : ℕ}
    {p shift : ℤ} (H : SourceBandBankData.Stored μ fB fC header NB NC g h J (2 * h * J) occ p shift)
    (hs : s < LightBlockSourceCatalog.count h J) (hi : i < SourceBandPairSlices.count NB NC g)
    (hj : j < SourceBandPairSlices.count NB NC g) (hw : (lim.space : ℤ) ≤ lim.word)
    (hK : K ≤ LightSwitchDepth.depth J + 1)
    (hsource : SourceBandBankData.finish header NB NC g h J (2 * h * J) ≤ record) (hrecords : record + 5 * K ≤ base)
    (R : LightSharedReportingLevels.Resources lim base h J K g g (d + 1)) :
    Meets lim program 65 d
      [h, J, K, SourceBandBankData.first header, SourceBandBankLayout.span h J (2 * h * J), s, i, j, localChoose h,
        localPairs h, record, base]
      μ (time h J K)
      (fun result ν =>
        result = (baseAt base h J K : ℤ) ∧
          Built ν record base h J K
              (leftSource p (SourceBandPartition.source NB g i) (fun t : Fin NB => fB t.val) (representative h J s))
              (rightSource p shift (SourceBandPartition.source NC g j) (fun t : Fin NC => fC t.val)
                (representative h J s)) ∧
            Kept μ ν record ∧ KeptBut μ ν base record (5 * K)) :=
  by
  have hleft := source_bounds (base := header) (cut := 2 * h * J) hi hs
  have hright := source_bounds (base := header) (cut := 2 * h * J) hj hs
  have hdata := source_pair H hi hj hs
  have hspace := R.space
  have hdepth := R.widthDepth
  have hstate := R.state
  have hbase : base ≤ lim.space := (Nat.le_add_right _ _).trans hspace
  have hleftAddr : leftCell header h J (2 * h * J) i s < record := hleft.1.trans_le hsource
  have hrightAddr : rightCell header h J (2 * h * J) j s < record := hright.2.1.trans_le hsource
  have hlNat : SourceBandBankData.first header + i * SourceBandBankLayout.span h J (2 * h * J) + 2 * s < lim.space :=
    hleftAddr.trans_le (by omega)
  have hrNat :
    SourceBandBankData.first header + j * SourceBandBankLayout.span h J (2 * h * J) + 2 * s + 1 < lim.space :=
    hrightAddr.trans_le (by omega)
  have hlZ :
    (SourceBandBankData.first header : ℤ) + (i : ℤ) * (SourceBandBankLayout.span h J (2 * h * J) : ℤ) + 2 * (s : ℤ) <
      (lim.space : ℤ) :=
    by exact_mod_cast hlNat
  have hrZ :
    (SourceBandBankData.first header : ℤ) + (j : ℤ) * (SourceBandBankLayout.span h J (2 * h * J) : ℤ) + 2 * (s : ℤ) +
        1 <
      (lim.space : ℤ) :=
    by exact_mod_cast hrNat
  have hiNZ : (0 : ℤ) ≤ (i : ℤ) * (SourceBandBankLayout.span h J (2 * h * J) : ℤ) := by positivity
  have hjNZ : (0 : ℤ) ≤ (j : ℤ) * (SourceBandBankLayout.span h J (2 * h * J) : ℤ) := by positivity
  apply Meets.of_body (p := 65) (by rfl : program[65]? = some (body 64))
  unfold body time
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen (leftCell header h J (2 * h * J) i s : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, leftCell, bankBase,
            SourceBandBankLayout.baseAt]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [leftCell, bankBase, SourceBandBankLayout.baseAt] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, leftCell, bankBase,
            SourceBandBankLayout.baseAt] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen (rightCell header h J (2 * h * J) j s : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, rightCell, bankBase,
            SourceBandBankLayout.baseAt]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [rightCell, bankBase, SourceBandBankLayout.baseAt] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, rightCell, bankBase,
            SourceBandBankLayout.baseAt] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  have hc :=
    (LightSharedReportingLevels.program_meets (d := d + 1) (record := record) (base := base)
          (leftSource p (SourceBandPartition.source NB g i) (fun t : Fin NB => fB t.val) (representative h J s))
          (rightSource p shift (SourceBandPartition.source NC g j) (fun t : Fin NC => fC t.val) (representative h J s))
          hw hK hrecords hleftAddr hrightAddr (hleft.2.2.1.trans hsource) (hright.2.2.2.trans hsource) R
          (fun S _ => left_abs_le p NB g i h J s fB S) (fun S _ => right_abs_le p shift NC g j h J s fC S) hdata.1
          hdata.2.1 hdata.2.2.1 hdata.2.2.2).append
      [body 64]
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    first
    | refine _root_.Light.Ends.callToThen (hc _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hc ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
    on_goal -1 =>
      (rintro result ν ⟨hresult, hbuilt, hkeep, hkeepBlock⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen (baseAt base h J K : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hresult]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hresult] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hresult] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  exact ⟨rfl, hbuilt, hkeep, hkeepBlock⟩
end ThreeSum.LightSharedReportingPair
