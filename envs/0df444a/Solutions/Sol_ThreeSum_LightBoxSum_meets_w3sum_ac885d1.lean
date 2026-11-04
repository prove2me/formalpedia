-- Prove2me | solution 1 for ThreeSum.LightBoxSum.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:05:57.93352+00:00
-- url     : https://prove2.me/submissions/96b7968e-2919-4413-a88b-e5545c17bb51

import Definitions.Def_Submission_ThreeSum_LightQueryBox
import Definitions.Def_Submission_ThreeSum_BoxBounds
import Definitions.Def_Submission_ThreeSum_LightBoxSum
import Theorems.Thm_ThreeSum_LightBoxSum_partialSum_succ
import Theorems.Thm_ThreeSum_LightBoxSum_partialSum_length
import Theorems.Thm_Light_Ends_pieceThen
import Theorems.Thm_Light_Limits_Addr_abs_le
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_SameOn_refl
import Theorems.Thm_Light_SameOutside2_refl
import Theorems.Thm_Light_SameOutside_refl
import Theorems.Thm_Light_SegN_getElem
import Theorems.Thm_Light_frame_append_zeros
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_List_abs_sum_take_map_le
import Theorems.Thm_ThreeSumApsp_AbsLe_getElem
import Definitions.Def_WeightedCache3SUM_Alias_d3c4667101dfdda3
import Theorems.Thm_ThreeSum_BoxStages_mem_prefix
import Theorems.Thm_ThreeSum_BoxStages_prefix_all
import Theorems.Thm_ThreeSum_BoxStages_prefix_zero
import Theorems.Thm_ThreeSum_BoxStages_stageValue_all
import Theorems.Thm_ThreeSum_BoxStages_stageValue_zero
import Definitions.Def_WeightedCache3SUM_Alias_180c3abfd6d390ad
import Definitions.Def_WeightedCache3SUM_Alias_673095557addf664
import Definitions.Def_WeightedCache3SUM_Alias_31257a44f822c74e
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_2ab790e73b946b9f
import Definitions.Def_WeightedCache3SUM_Alias_e3ff37f6db941441
import Definitions.Def_WeightedCache3SUM_Alias_5c1e55e66cf081b7
import Definitions.Def_WeightedCache3SUM_Alias_f29d07b5f5ce2e2c
import Definitions.Def_WeightedCache3SUM_Alias_098d503c7eb426c7
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_length
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_zero
import Definitions.Def_WeightedCache3SUM_Alias_037fdff845f4735d
import Definitions.Def_WeightedCache3SUM_Alias_8a94481881de516b
import Definitions.Def_WeightedCache3SUM_Alias_c0e528b1e0cee255
import Definitions.Def_WeightedCache3SUM_Alias_44f02ed11cdb23f7
import Definitions.Def_WeightedCache3SUM_Alias_d110f06b53aa1a96
import Definitions.Def_WeightedCache3SUM_Alias_197272b1cee37ac5
import Theorems.Thm_ThreeSum_MaskDifference_subsetMask_empty
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_subsetRank_lt
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
import Theorems.Thm_ThreeSum_SubsetStages_mem_suffix
import Theorems.Thm_ThreeSum_SubsetStages_stageValue_all
import Theorems.Thm_ThreeSum_SubsetStages_stageValue_zero
import Theorems.Thm_ThreeSum_SubsetStages_suffix_all
import Theorems.Thm_ThreeSum_SubsetStages_suffix_zero
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.BoxStages.mem_prefix
attribute [local simp] ThreeSum.BoxStages.prefix_all
attribute [local simp] ThreeSum.BoxStages.prefix_zero
attribute [local simp] ThreeSum.BoxStages.stageValue_all
attribute [local simp] ThreeSum.BoxStages.stageValue_zero
attribute [local simp] ThreeSum.LightSubsetEnumeration.output_length
attribute [local simp] ThreeSum.LightSubsetEnumeration.output_zero
attribute [local simp] ThreeSum.MaskDifference.subsetMask_empty
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
attribute [local simp] ThreeSum.SubsetStages.mem_suffix
attribute [local simp] ThreeSum.SubsetStages.stageValue_all
attribute [local simp] ThreeSum.SubsetStages.stageValue_zero
attribute [local simp] ThreeSum.SubsetStages.suffix_all
attribute [local simp] ThreeSum.SubsetStages.suffix_zero
attribute [local simp] ThreeSum.LightBoxSum.partialSum_length
set_option autoImplicit false
open ThreeSum ThreeSum.LightBoxSum
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightBoxSum
theorem _root_.solution
    {pMain pBox pMinimum pLookup pSize pAddress pSetup pBuild pFill pRow pLinear pPowers pRank pOffset pErase : ℕ}
    (hmain : P[pMain]? = some (body pBox)) (hBox : P[pBox]? = some (LightQueryBox.body pMinimum pLookup))
    (hMinimum : P[pMinimum]? = some (LightMaskMinimum.body pPowers pErase))
    (hLookup : P[pLookup]? = some (LightStageLookup.body pSize pAddress))
    (hSize : P[pSize]? = some (LightDownsetSize.body pSetup pOffset))
    (hAddress : P[pAddress]? = some (LightDownsetAddress.body pSetup pOffset))
    (C : LightSubsetSetup.Procs P pSetup pBuild pFill pRow pLinear pPowers pRank)
    (hOffset : P[pOffset]? = some LightSubsetOffset.body) (hErase : P[pErase]? = some (LightMaskErase.body pErase))
    {μ : ℕ → ℤ} {L cut t maskBase base work B d : ℕ} (Q : Finset (Fin L)) (missing : List (Finset (Fin L)))
    (weight : Finset (Fin L) → ℤ) (hw : (lim.space : ℤ) ≤ lim.word) (hcut : cut ≤ L)
    (hdata : base + (L + 1) * downsetCap L cut ≤ work) (hmasks : maskBase + missing.length ≤ work)
    (hspace : work + tableSize L + (L + 1) ≤ lim.space) (hword : (((L + 1) * 2 ^ (L + 1) : ℕ) : ℤ) ≤ lim.word)
    (haccWord : ((missing.length * (2 ^ L * B) : ℕ) : ℤ) ≤ lim.word)
    (hvalid : ∀ U ∈ missing, U ⊆ Q ∧ U.card = t ∧ (Q \ U).card ≤ cut) (hweight : ∀ S, S.card ≤ cut → |weight S| ≤ B)
    (hstored : LightBoxStages.StoredThrough μ base cut weight L) (hseg : SegN μ maskBase (missing.map subsetMask))
    (hd : d + L + 7 ≤ lim.depth) :
    Meets lim P pMain d [L, cut, Q.card, subsetMask Q, t, missing.length, maskBase, base, work] μ
      (time L missing.length) (fun r μ' => r = (missing.map (boxValue Q weight)).sum ∧ Kept μ μ' work) :=
  by
  have hboxBound : ∀ U ∈ missing, |boxValue Q weight U| ≤ ((2 ^ L * B : ℕ) : ℤ) :=
    by
    intro U hU
    exact BoxBounds.boxSum_abs_le (Q \ U) (SparseBoxes.queryFree Q U) weight (hvalid U hU).2.2 hweight
  have hacc (j : ℕ) : |partialSum Q weight missing j| ≤ lim.word :=
    by
    have hh := List.abs_sum_take_map_le missing (boxValue Q weight) hboxBound j
    have hb : (missing.length : ℤ) * ((2 ^ L * B : ℕ) : ℤ) ≤ lim.word := by simpa only [Nat.cast_mul] using haccWord
    exact hh.trans hb
  have haddr (j : ℕ) (hj : j ≤ L) (S : Finset (Fin L)) (hS : S.card ≤ cut) :
    LightBoxStages.stageBase base (downsetCap L cut) j + subsetRank S < work :=
    by
    have hr := subsetRank_lt hS
    have hm := Nat.mul_le_mul_right (downsetCap L cut) (Nat.succ_le_succ hj)
    unfold LightBoxStages.stageBase
    simp only [Nat.succ_mul, Nat.add_mul, Nat.one_mul] at hm hdata
    omega
  apply Meets.of_body hmain
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
    refine _root_.Light.Ends.setToThen (0 : ℕ) ?_ ?_ ?_
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
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  refine
    Ends.pieceThen
      (Ends.for (T := missing.length * (LightQueryBox.time L + 50) + 20) (Q :=
        Inv μ Q weight missing cut t maskBase base work missing.length)
        (Inv μ Q weight missing cut t maskBase base work) missing.length (LightQueryBox.time L + 40) ?start ?round ?done
        ?bound (hT := by
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [] <;> first
              | omega
              | (ring_nf; omega))))
      ?after
  case start =>
    refine ⟨0, μ, ?_, SameOn.refl⟩
    simp [update_frame_setLocal, partialSum]
    change
      frame [(L : ℤ), cut, Q.card, subsetMask Q, t, missing.length, maskBase, base, work, 0, 0] =
        frame ([(L : ℤ), cut, Q.card, subsetMask Q, t, missing.length, maskBase, base, work, 0, 0] ++ [0])
    exact (frame_append_zeros _ 1).symm
  case round =>
    rintro j _ hj _ ⟨r, μ', rfl, hkept⟩
    let U := missing[j]
    have hU := hvalid U (List.getElem_mem hj)
    have hstored' : LightBoxStages.StoredThrough μ' base cut weight L :=
      by
      intro i hi S hS
      exact (hkept _ (haddr i hi S hS)).trans (hstored i hi S hS)
    have hmask : μ' (maskBase + j) = (subsetMask U : ℤ) :=
      by
      have hr := hseg.getElem (by simpa using hj)
      simp only [List.getElem_map] at hr
      exact (hkept _ (by omega)).trans hr
    have hc :=
      LightQueryBox.meets (d := d + 1) hBox hMinimum hLookup hSize hAddress C hOffset hErase Q U weight hw hcut hdata
        hspace hword hU.1 hU.2.2 hstored' (by omega)
    rw [hU.2.1] at hc
    unfold roundBody
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
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hmask,
              LightQueryBox.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hmask, LightQueryBox.time] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hmask, LightQueryBox.time] <;> omega)
      on_goal -1 => (rintro res μ₁ ⟨hres, hnewKept⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    have hnext := abs_le.mp (hacc (j + 1))
    have hsum : partialSum Q weight missing j + boxValue Q weight U = partialSum Q weight missing (j + 1) :=
      (partialSum_succ Q weight missing hj).symm
    have hres' : res = boxValue Q weight U := hres
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        (repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_))
      refine _root_.Light.Ends.setToThen (partialSum Q weight missing (j + 1)) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hres', hsum,
              LightQueryBox.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hres', hsum, LightQueryBox.time] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hres', hsum, LightQueryBox.time] <;> omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    refine ⟨by simp, res, μ₁, ?_, hkept.trans hnewKept⟩
    simp [update_frame_setLocal]
  case done =>
    intro σ _ h
    exact h
  case bound =>
    rintro j _ hj _ ⟨r, μ', rfl, _⟩
    ( (try have := _root_.Light.Std.space_le (by assumption))
      (try have := _root_.Light.Std.const_le (by assumption))
      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
  case after =>
    rintro _ ⟨r, μ', rfl, hkept⟩
    have ha := abs_le.mp (hacc missing.length)
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        (repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_))
      refine _root_.Light.Ends.setToThen ((missing.map (boxValue Q weight)).sum) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, partialSum_length]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [partialSum_length] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, partialSum_length] <;> omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    exact ⟨by simp, hkept⟩
end ThreeSum.LightBoxSum
