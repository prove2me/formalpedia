-- Prove2me | solution 1 for ThreeSum.LightQueryBox.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:55:07.88278+00:00
-- url     : https://prove2.me/submissions/7b03bca1-3f68-49b4-9542-f25f2faf1efa

import Definitions.Def_Submission_ThreeSum_LightStageLookup
import Definitions.Def_Submission_ThreeSum_LightMaskMinimum
import Definitions.Def_Submission_ThreeSum_MaskDifference
import Definitions.Def_Submission_ThreeSum_LightQueryBox
import Theorems.Thm_Light_Ends_iteLast
import Theorems.Thm_Light_Ends_pieceThen
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_SameOn_refl
import Theorems.Thm_Light_SameOutside2_refl
import Theorems.Thm_Light_SameOutside_refl
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_BoxStages_mem_prefix
import Theorems.Thm_ThreeSum_BoxStages_prefix_all
import Theorems.Thm_ThreeSum_BoxStages_prefix_zero
import Theorems.Thm_ThreeSum_BoxStages_stageValue_all
import Theorems.Thm_ThreeSum_BoxStages_stageValue_zero
import Definitions.Def_WeightedCache3SUM_Alias_180c3abfd6d390ad
import Theorems.Thm_ThreeSum_LightBoxStages_stored_box_lookup
import Theorems.Thm_ThreeSum_LightBoxStages_stored_query_box
import Definitions.Def_WeightedCache3SUM_Alias_673095557addf664
import Definitions.Def_WeightedCache3SUM_Alias_31257a44f822c74e
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_2ab790e73b946b9f
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
import Theorems.Thm_ThreeSum_MaskDifference_subsetMask_eq_zero_iff
import Theorems.Thm_ThreeSum_MaskDifference_subsetMask_sdiff_int
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_subsetMask_isMask
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
set_option autoImplicit false
open ThreeSum ThreeSum.LightQueryBox
open Light ThreeSum.SubsetAddress ThreeSum.MaskDifference
open ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightQueryBox
theorem _root_.solution
    {pMain pMinimum pLookup pSize pAddress pSetup pBuild pFill pRow pLinear pPowers pRank pOffset pErase : ℕ}
    (hmain : P[pMain]? = some (body pMinimum pLookup))
    (hMinimum : P[pMinimum]? = some (LightMaskMinimum.body pPowers pErase))
    (hLookup : P[pLookup]? = some (LightStageLookup.body pSize pAddress))
    (hSize : P[pSize]? = some (LightDownsetSize.body pSetup pOffset))
    (hAddress : P[pAddress]? = some (LightDownsetAddress.body pSetup pOffset))
    (C : LightSubsetSetup.Procs P pSetup pBuild pFill pRow pLinear pPowers pRank)
    (hOffset : P[pOffset]? = some LightSubsetOffset.body) (hErase : P[pErase]? = some (LightMaskErase.body pErase))
    {μ : ℕ → ℤ} {L cut base work d : ℕ} (Q U : Finset (Fin L)) (weight : Finset (Fin L) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hcut : cut ≤ L) (hdata : base + (L + 1) * downsetCap L cut ≤ work)
    (hspace : work + tableSize L + (L + 1) ≤ lim.space) (hword : (((L + 1) * 2 ^ (L + 1) : ℕ) : ℤ) ≤ lim.word)
    (hU : U ⊆ Q) (hflags : (Q \ U).card ≤ cut) (hstored : LightBoxStages.StoredThrough μ base cut weight L)
    (hd : d + L + 6 ≤ lim.depth) :
    Meets lim P pMain d [L, cut, Q.card, subsetMask Q, U.card, subsetMask U, base, work] μ (time L)
      (fun r μ' => r = SparseBoxes.boxSum (Q \ U) (SparseBoxes.queryFree Q U) weight ∧ Kept μ μ' work) :=
  by
  have hword₀ : ((2 ^ (L + 1) : ℕ) : ℤ) ≤ lim.word :=
    by
    have hh : (2 ^ (L + 1) : ℕ) ≤ (L + 1) * 2 ^ (L + 1) := Nat.le_mul_of_pos_left _ (by omega)
    exact (by exact_mod_cast hh : ((2 ^ (L + 1) : ℕ) : ℤ) ≤ (((L + 1) * 2 ^ (L + 1) : ℕ) : ℤ)).trans hword
  have hpow : (2 ^ L : ℕ) ≤ 2 ^ (L + 1) := Nat.pow_le_pow_right (by decide) (by omega)
  have hpowZ : ((2 ^ L : ℕ) : ℤ) ≤ lim.word :=
    (by exact_mod_cast hpow : ((2 ^ L : ℕ) : ℤ) ≤ ((2 ^ (L + 1) : ℕ) : ℤ)).trans hword₀
  have hcardle := Finset.card_le_card hU
  have hcardDiff := Finset.card_sdiff_of_subset hU
  have hcard : (Q.card : ℤ) - (U.card : ℤ) = ((Q \ U).card : ℤ) := by omega
  have hmask := subsetMask_sdiff_int Q U hU
  have hmaskBound : (subsetMask (Q \ U) : ℤ) < ((2 ^ L : ℕ) : ℤ) := by exact_mod_cast (subsetMask_isMask (Q \ U)).1
  have hmaskNonneg : (0 : ℤ) ≤ subsetMask (Q \ U) := Int.natCast_nonneg _
  have hr := subsetRank_lt hflags
  have haddr (j : ℕ) (hj : j ≤ L) : LightStageLookup.readAddr cut base j (Q \ U) < work :=
    by
    have hm := Nat.mul_le_mul_right (downsetCap L cut) (Nat.succ_le_succ hj)
    unfold LightStageLookup.readAddr
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
    refine _root_.Light.Ends.setToThen ((Q \ U).card : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hcard, LightMaskMinimum.time,
            LightStageLookup.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hcard, LightMaskMinimum.time, LightStageLookup.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hcard, LightMaskMinimum.time,
            LightStageLookup.time] <;> omega)
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
    refine _root_.Light.Ends.setToThen (subsetMask (Q \ U) : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hmask, LightMaskMinimum.time,
            LightStageLookup.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hmask, LightMaskMinimum.time, LightStageLookup.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hmask, LightMaskMinimum.time,
            LightStageLookup.time] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  refine
    Ends.pieceThen
      (Ends.iteLast (T := LightMaskMinimum.time L + 20) (Q := fun σ =>
        ∃ (j : ℕ),
          j ≤ L ∧
            σ.loc =
                frame
                  (setLocal
                    (setLocal
                      (setLocal [L, cut, Q.card, subsetMask Q, U.card, subsetMask U, base, work] 8 ((Q \ U).card : ℤ)) 9
                      (subsetMask (Q \ U) : ℤ))
                    10 (j : ℤ)) ∧
              Kept μ σ.mem work ∧
                σ.mem (LightStageLookup.readAddr cut base j (Q \ U)) =
                  SparseBoxes.boxSum (Q \ U) (SparseBoxes.queryFree Q U) weight)
        ?zero ?nonzero
        (by (
            (try have := _root_.Light.Std.space_le (by assumption))
            (try have := _root_.Light.Std.const_le (by assumption))
            simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
        (hT := by
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil,
              LightMaskMinimum.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [LightMaskMinimum.time] <;> first
              | omega
              | (ring_nf; omega))))
      ?after (hT := by
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightMaskMinimum.time,
            LightStageLookup.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightMaskMinimum.time, LightStageLookup.time] <;> first
            | omega
            | (ring_nf; omega)))
  case zero =>
    intro hz
    have hz' : subsetMask U = 0 := by exact_mod_cast (by simpa using hz : (subsetMask U : ℤ) = 0)
    have hUempty := (subsetMask_eq_zero_iff U).mp hz'
    have hread :
      μ (LightStageLookup.readAddr cut base L (Q \ U)) =
        SparseBoxes.boxSum (Q \ U) (SparseBoxes.queryFree Q U) weight :=
      by
      have hh := LightBoxStages.stored_box_lookup hstored le_rfl (Q \ U) hflags
      simpa [LightStageLookup.readAddr, LightBoxStages.stageBase, SparseBoxes.queryFree, hUempty] using hh
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        (repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_))
      refine _root_.Light.Ends.setToThen (L : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil,
              LightMaskMinimum.time, LightStageLookup.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [LightMaskMinimum.time, LightStageLookup.time] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightMaskMinimum.time,
              LightStageLookup.time] <;> omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    exact ⟨L, le_rfl, rfl, SameOn.refl, hread⟩
  case nonzero =>
    intro hz
    have hUpos : U.Nonempty := by
      apply Finset.nonempty_iff_ne_empty.mpr
      intro he
      apply hz
      simp [he, subsetMask_empty]
    have hm :=
      LightMaskMinimum.meets (d := d + 1) (μ := μ) (work := work) hMinimum C.powers hErase U hUpos hw (by omega) hword₀
        (by omega)
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
      | refine _root_.Light.Ends.callToThen (hm _ (by omega)) ?_ ?_ ?_ ?_
      | refine _root_.Light.Ends.callToThen hm ?_ ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil,
              LightMaskMinimum.time, LightStageLookup.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [LightMaskMinimum.time, LightStageLookup.time] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightMaskMinimum.time,
              LightStageLookup.time] <;> omega)
      on_goal -1 => (rintro smallest μ₁ ⟨hsmallest, hminKept⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    refine ⟨(U.min' hUpos).val, Nat.le_of_lt (U.min' hUpos).isLt, ?_, hminKept, ?_⟩
    · simp only [hsmallest]
    · have hh := LightBoxStages.stored_query_box hstored Q U hUpos hflags
      exact (hminKept _ (haddr _ (Nat.le_of_lt (U.min' hUpos).isLt))).trans hh
  case after =>
    rintro σ ⟨j, hj, hloc, hkept, hread⟩
    rcases σ with ⟨loc, μ'⟩
    simp only at hloc hkept hread
    subst loc
    have hc :=
      LightStageLookup.meets (d := d + 1) hLookup hSize hAddress C hOffset (Q \ U)
        (SparseBoxes.boxSum (Q \ U) (SparseBoxes.queryFree Q U) weight) hw hcut hdata hspace hword hflags hj hread
        (by omega)
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
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil,
              LightMaskMinimum.time, LightStageLookup.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [LightMaskMinimum.time, LightStageLookup.time] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightMaskMinimum.time,
              LightStageLookup.time] <;> omega)
      on_goal -1 => (rintro res μ₁ ⟨hres, hnewKept⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    exact ⟨hres, hkept.trans hnewKept⟩
end ThreeSum.LightQueryBox
