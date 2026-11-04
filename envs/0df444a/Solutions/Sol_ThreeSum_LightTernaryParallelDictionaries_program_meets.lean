-- Prove2me | solution 1 for ThreeSum.LightTernaryParallelDictionaries.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:00:00.665428+00:00
-- url     : https://prove2.me/submissions/d6081e1b-d5c0-43dd-9107-8d8849d7781b

import Definitions.Def_Submission_ThreeSum_LightFixedRadixDictionary
import Definitions.Def_Submission_ThreeSum_ReportingHostRelocation
import Definitions.Def_Submission_ThreeSum_LightTernaryParallelDictionaries
import Theorems.Thm_Light_Ends_append
import Theorems.Thm_Light_Exec_append
import Theorems.Thm_Light_Meets_append
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSumApsp_AbsLe_append
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_LightFiniteTable_meets
import Theorems.Thm_ThreeSum_LightFiniteTable_program_meets
import Theorems.Thm_ThreeSum_LightFixedRadixDictionary_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_4b4040d8de1fb856
import Theorems.Thm_ThreeSum_LightRadixKeys_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_32e47c9a32bb047b
import Theorems.Thm_ThreeSum_LightRadixRows_program_meets
import Theorems.Thm_ThreeSum_LightReportingAffine_meets
import Theorems.Thm_ThreeSum_LightReportingAffine_program_meets
import Theorems.Thm_ThreeSum_LightSignedFiniteTable_meets
import Theorems.Thm_ThreeSum_LightSignedFiniteTable_program_meets
import Theorems.Thm_ThreeSum_RadixKeyLists_values_length
import Theorems.Thm_ThreeSum_ReportingHostRelocation_meets
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryParallelDictionaries
open Light RadixKeyLists
set_option maxHeartbeats 3000000
set_option maxRecDepth 16000
variable {lim : Limits}
namespace ThreeSum.LightTernaryParallelDictionaries
theorem _root_.solution (xs ys zs : List ℤ) {base0 dst0 base1 dst1 base2 dst2 p0 p1 p2 U0 U1 U2 J d : ℕ} (μ : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hbase0 : base0 + xs.length ≤ dst0)
    (hnext0 : LightRadixKeys.space dst0 xs.length J ≤ base1) (hbase1 : base1 + ys.length ≤ dst1)
    (hnext1 : LightRadixKeys.space dst1 ys.length J ≤ base2) (hbase2 : base2 + zs.length ≤ dst2)
    (hspace2 : LightRadixKeys.space dst2 zs.length J ≤ lim.space) (hm0 : 0 < xs.length) (hm1 : 0 < ys.length)
    (hm2 : 0 < zs.length) (hb0 : ∀ x ∈ xs, |x| ≤ (U0 : ℤ)) (hb1 : ∀ x ∈ ys, |x| ≤ (U1 : ℤ))
    (hb2 : ∀ x ∈ zs, |x| ≤ (U2 : ℤ)) (hw0 : (LightRadixKeys.word p0 U0 J : ℤ) ≤ lim.word)
    (hw1 : (LightRadixKeys.word p1 U1 J : ℤ) ≤ lim.word) (hw2 : (LightRadixKeys.word p2 U2 J : ℤ) ≤ lim.word)
    (hd : d + J + 4 ≤ lim.depth) :
    Meets lim (program xs ys zs) 15 d [base0, dst0, base1, dst1, base2, dst2, J, p0, p1, p2] μ (time xs ys zs J)
      (fun r ν =>
        r = ((dst2 + LightRadixKeys.offset zs.length J : ℕ) : ℤ) ∧
          output ν dst0 xs p0 J ∧ output ν dst1 ys p1 J ∧ output ν dst2 zs p2 J ∧ Kept μ ν base0) :=
  by
  have hdst2 : dst2 ≤ lim.space := by unfold LightRadixKeys.space at hspace2; omega
  have hspace1 : LightRadixKeys.space dst1 ys.length J ≤ lim.space := by omega
  have hdst1 : dst1 ≤ lim.space := by unfold LightRadixKeys.space at hspace1; omega
  have hspace0 : LightRadixKeys.space dst0 xs.length J ≤ lim.space := by omega
  have h0 :=
    ((LightFixedRadixDictionary.program_meets xs (d := d + 1) μ hw hbase0 hm0 hb0 hspace0 hw0 (by omega)).append
          (LightFixedRadixDictionary.program ys |>.map (ReportingHostRelocation.relocate 5))).append
      ((LightFixedRadixDictionary.program zs |>.map (ReportingHostRelocation.relocate 10)) ++ [body])
  have h0' :
    Meets lim (program xs ys zs) 4 (d + 1) [base0, dst0, J, p0] μ (LightFixedRadixDictionary.time xs J)
      (fun r ν => r = ((dst0 + LightRadixKeys.offset xs.length J : ℕ) : ℤ) ∧ output ν dst0 xs p0 J ∧ Kept μ ν base0) :=
    by
    simpa only [program, libraries, ReportingHostRelocation.program, List.length_cons, List.length_nil,
      LightFixedRadixDictionary.program, List.length_append, List.length_map, Nat.reduceAdd, List.append_assoc, output,
      and_assoc] using h0
  apply Meets.of_body (by rfl : (program xs ys zs)[15]? = some body)
  unfold body time
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_)
    first
    | refine _root_.Light.Ends.callToThen (h0' _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen h0' ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightFixedRadixDictionary.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightFixedRadixDictionary.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightFixedRadixDictionary.time] <;> omega)
    on_goal -1 => (rintro head0 μ0 ⟨hhead0, hout0, hkeep0⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have h1 :=
    (ReportingHostRelocation.meets
          (LightFixedRadixDictionary.program_meets ys (d := d + 1) μ0 hw hbase1 hm1 hb1 hspace1 hw1 (by omega))
          (LightFixedRadixDictionary.program xs)).append
      ((LightFixedRadixDictionary.program zs |>.map (ReportingHostRelocation.relocate 10)) ++ [body])
  have h1' :
    Meets lim (program xs ys zs) 9 (d + 1) [base1, dst1, J, p1] μ0 (LightFixedRadixDictionary.time ys J)
      (fun r ν => r = ((dst1 + LightRadixKeys.offset ys.length J : ℕ) : ℤ) ∧ output ν dst1 ys p1 J ∧ Kept μ0 ν base1) :=
    by
    simpa only [program, libraries, ReportingHostRelocation.program, List.length_cons, List.length_nil,
      LightFixedRadixDictionary.program, List.length_append, List.length_map, Nat.reduceAdd, List.append_assoc, output,
      and_assoc] using h1
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_)
    first
    | refine _root_.Light.Ends.callToThen (h1' _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen h1' ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightFixedRadixDictionary.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightFixedRadixDictionary.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightFixedRadixDictionary.time] <;> omega)
    on_goal -1 => (rintro head1 μ1 ⟨hhead1, hout1, hkeep1⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have h2 :=
    (ReportingHostRelocation.meets
          (LightFixedRadixDictionary.program_meets zs (d := d + 1) μ1 hw hbase2 hm2 hb2 hspace2 hw2 (by omega))
          (ReportingHostRelocation.program (LightFixedRadixDictionary.program xs)
            (LightFixedRadixDictionary.program ys))).append
      [body]
  have h2' :
    Meets lim (program xs ys zs) 14 (d + 1) [base2, dst2, J, p2] μ1 (LightFixedRadixDictionary.time zs J)
      (fun r ν => r = ((dst2 + LightRadixKeys.offset zs.length J : ℕ) : ℤ) ∧ output ν dst2 zs p2 J ∧ Kept μ1 ν base2) :=
    by
    simpa only [program, libraries, ReportingHostRelocation.program, List.length_cons, List.length_nil,
      LightFixedRadixDictionary.program, List.length_append, List.length_map, Nat.reduceAdd, List.append_assoc, output,
      and_assoc] using h2
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_)
    first
    | refine _root_.Light.Ends.callToThen (h2' _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen h2' ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightFixedRadixDictionary.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightFixedRadixDictionary.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightFixedRadixDictionary.time] <;> omega)
    on_goal -1 => (rintro head2 ν ⟨hhead2, hout2, hkeep2⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_)
    refine _root_.Light.Ends.setToThen (dst2 + LightRadixKeys.offset zs.length J : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hhead2, LightFixedRadixDictionary.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hhead2, LightFixedRadixDictionary.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hhead2, LightFixedRadixDictionary.time] <;>
          omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  change
    ((dst2 + LightRadixKeys.offset zs.length J : ℕ) : ℤ) = _ ∧
      output ν dst0 xs p0 J ∧ output ν dst1 ys p1 J ∧ output ν dst2 zs p2 J ∧ Kept μ ν base0
  refine ⟨rfl, ?_, ?_, hout2, ?_⟩
  · rcases hout0 with ⟨hheader, hseg⟩
    constructor
    · rw [hkeep2 _ (by unfold LightRadixKeys.space at hnext0 hnext1; omega),
        hkeep1 _ (by unfold LightRadixKeys.space at hnext0; omega)]
      exact hheader
    · intro a ha
      rw [hkeep2 _ (by rw [values_length] at ha; unfold LightRadixKeys.space at hnext0 hnext1; omega),
        hkeep1 _ (by rw [values_length] at ha; unfold LightRadixKeys.space at hnext0; omega)]
      exact hseg a ha
  · rcases hout1 with ⟨hheader, hseg⟩
    constructor
    · rw [hkeep2 _ (by unfold LightRadixKeys.space at hnext1; omega)]
      exact hheader
    · intro a ha
      rw [hkeep2 _ (by rw [values_length] at ha; unfold LightRadixKeys.space at hnext1; omega)]
      exact hseg a ha
  · intro a ha
    rw [hkeep2 a (by unfold LightRadixKeys.space at hnext0 hnext1; omega),
      hkeep1 a (by unfold LightRadixKeys.space at hnext0; omega), hkeep0 a ha]
end ThreeSum.LightTernaryParallelDictionaries
