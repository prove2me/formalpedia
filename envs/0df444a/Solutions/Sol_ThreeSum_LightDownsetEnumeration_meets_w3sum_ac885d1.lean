-- Prove2me | solution 1 for ThreeSum.LightDownsetEnumeration.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:06:45.100614+00:00
-- url     : https://prove2.me/submissions/85283be3-851b-4ab2-90cc-ef1d0bc748ab

import Definitions.Def_Submission_ThreeSum_LightSubsetEnumerationSetup
import Definitions.Def_Submission_ThreeSum_LightDownsetEnumeration
import Theorems.Thm_ThreeSum_LightDownsetEnumeration_layers_length
import Theorems.Thm_ThreeSum_LightDownsetEnumeration_layers_eq_downset
import Theorems.Thm_ThreeSum_LightDownsetEnumeration_layer_time_le_budget
import Theorems.Thm_Light_Ends_pieceThen
import Theorems.Thm_Light_Meets_mono_time
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_SameOn_refl
import Theorems.Thm_Light_SameOutside2_refl
import Theorems.Thm_Light_SameOutside_refl
import Theorems.Thm_Light_SegN_of_sameOutside
import Theorems.Thm_Light_Seg_of_sameOutside
import Theorems.Thm_Light_frame_append_zeros
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Definitions.Def_WeightedCache3SUM_Alias_04c57512725a2a98
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Definitions.Def_WeightedCache3SUM_Alias_f29d07b5f5ce2e2c
import Definitions.Def_WeightedCache3SUM_Alias_098d503c7eb426c7
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_length
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_zero
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_mono
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_succ
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
attribute [local simp] ThreeSum.LightSubsetEnumeration.output_length
attribute [local simp] ThreeSum.LightSubsetEnumeration.output_zero
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
set_option autoImplicit false
open ThreeSum ThreeSum.LightDownsetEnumeration
open Light ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightDownsetEnumeration
theorem _root_.solution {pMain pEnum L cut dst powers d : ℕ} {μ : ℕ → ℤ} (hmain : P[pMain]? = some (body pEnum))
    (henum : P[pEnum]? = some (LightSubsetEnumeration.body pEnum)) (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : powers + (L + 1) ≤ lim.space) (hword : ((2 ^ (L + 1) : ℕ) : ℤ) ≤ lim.word) (hcut : cut ≤ L)
    (hdst : dst + downsetCap L cut ≤ powers) (hpowers : Powers μ powers L) (hd : d + L + 1 ≤ lim.depth) :
    Meets lim P pMain d [L, cut, dst, powers] μ (time L cut)
      (fun r μ' =>
        r = (downsetCap L cut : ℤ) ∧ SegN μ' dst (enumerateDownset L cut) ∧ SameOutside μ μ' dst (downsetCap L cut)) :=
  by
  have hcap : layerOffset L (cut + 1) = downsetCap L cut := by simp [downsetCap, Nat.min_eq_left hcut]
  apply Meets.of_body hmain
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
    refine _root_.Light.Ends.setToThen (0 : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, budget]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [budget] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, budget] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  refine
    Ends.pieceThen
      (Ends.for (T := (cut + 1) * (budget L cut + 70) + 20) (Q := Inv μ L cut dst powers (cut + 1))
        (Inv μ L cut dst powers) (cut + 1) (budget L cut + 50) ?start ?round ?done ?bound (hT := by
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [] <;>
              first
              | omega
              | (ring_nf; omega))))
      ?after
  case start =>
    refine ⟨0, μ, ?_, ?_, SameOutside.refl⟩
    · simp [update_frame_setLocal, layerOffset_zero]
      exact (frame_append_zeros [(L : ℤ), cut, dst, powers, 0, 0] 1).symm
    · exact Seg.nil
  case round =>
    rintro j _ hj _ ⟨r, μ', rfl, hseg, hsame⟩
    have hjcut : j ≤ cut := by omega
    have hpart := layerOffset_mono L (show j + 1 ≤ cut + 1 by omega)
    rw [layerOffset_succ, hcap] at hpart
    have hpartial : dst + layerOffset L j ≤ powers := by omega
    have hnext : dst + layerOffset L j + L.choose j ≤ powers := by omega
    have hpowers' : Powers μ' powers L := by
      intro i hi
      rw [hsame (powers + i) (Or.inr (by omega))]
      exact hpowers i hi
    have hcall :=
      (LightSubsetEnumeration.meets henum hw hspace hword L j 0 (dst + layerOffset L j) μ' le_rfl (by omega) (by simp)
            hnext hpowers' (d + 1) (by omega)).mono_time
        (layer_time_le_budget hcut hjcut)
    unfold roundBody
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
      | refine _root_.Light.Ends.callToThen (hcall _ (by omega)) ?_ ?_ ?_ ?_
      | refine _root_.Light.Ends.callToThen hcall ?_ ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, budget]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [budget] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, budget] <;> omega)
      on_goal -1 => (rintro n μ₁ ⟨hn, hnew, hsame₁⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    have hnewN : SegN μ₁ (dst + layerOffset L j) (enumerateLayer L j) := by
      simpa [LightSubsetEnumeration.output] using hnew
    have hseg' : SegN μ₁ dst (layers L j) := hseg.of_sameOutside hsame₁ (Or.inl (by rw [layers_length]))
    have hsum : layerOffset L j + L.choose j ≤ lim.space := by omega
    have hsumZ : (layerOffset L j : ℤ) + (L.choose j : ℤ) ≤ lim.word :=
      by
      have hb : (layerOffset L j : ℤ) + (L.choose j : ℤ) ≤ (lim.space : ℤ) := by exact_mod_cast hsum
      exact hb.trans hw
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.setToThen (layerOffset L (j + 1) : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hn,
              layerOffset_succ, budget]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hn, layerOffset_succ, budget] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hn, layerOffset_succ, budget] <;> omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    refine ⟨by simp, n, μ₁, ?_, ?_, ?_⟩
    · simp [update_frame_setLocal]
    · change Seg μ₁ dst (((layers L j) ++ enumerateLayer L j).map _)
      rw [List.map_append, seg_append, List.length_map, layers_length]
      exact ⟨hseg', hnewN⟩
    ·
      exact
        hsame.then hsame₁
          (fun a ha => by
            rw [layerOffset_succ] at ha
            constructor <;> omega)
  case done =>
    intro σ _ hI
    exact hI
  case bound =>
    rintro j _ hj _ ⟨r, μ', rfl, _, _⟩
    ( (try have := _root_.Light.Std.space_le (by assumption))
      (try have := _root_.Light.Std.const_le (by assumption))
      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
  case after =>
    rintro _ ⟨r, μ', rfl, hseg, hsame⟩
    have hcZ : (downsetCap L cut : ℤ) ≤ lim.word :=
      by
      have hb : (downsetCap L cut : ℤ) ≤ (lim.space : ℤ) := by
        exact_mod_cast (show downsetCap L cut ≤ lim.space by omega)
      exact hb.trans hw
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.setToThen (downsetCap L cut : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hcap]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hcap] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hcap] <;> omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    exact ⟨by simp, by simpa only [layers_eq_downset hcut] using hseg, by simpa only [hcap] using hsame⟩
end ThreeSum.LightDownsetEnumeration
