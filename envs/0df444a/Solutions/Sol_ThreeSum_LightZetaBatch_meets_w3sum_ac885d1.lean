-- Prove2me | solution 1 for ThreeSum.LightZetaBatch.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:21:15.257194+00:00
-- url     : https://prove2.me/submissions/96a50386-db02-42c8-ac38-8033b7e25950

import Definitions.Def_Submission_ThreeSum_LightZetaCell
import Definitions.Def_Submission_ThreeSum_MaskDecode
import Definitions.Def_Submission_ThreeSum_LightZetaBatch
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
import Theorems.Thm_ThreeSumApsp_AbsLe_getElem
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_037fdff845f4735d
import Definitions.Def_WeightedCache3SUM_Alias_8a94481881de516b
import Definitions.Def_WeightedCache3SUM_Alias_44f02ed11cdb23f7
import Theorems.Thm_ThreeSum_MaskDecode_decode_card
import Theorems.Thm_ThreeSum_MaskDecode_subsetMask_decode
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_subsetMask_injective
import Theorems.Thm_ThreeSum_SubsetAddress_subsetRank_injective
import Theorems.Thm_ThreeSum_SubsetAddress_subsetRank_lt
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
set_option autoImplicit false
open ThreeSum ThreeSum.LightZetaBatch
open Light ThreeSum.SubsetAddress ThreeSum.LightZetaCell
open ThreeSum.MaskDecode
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightZetaBatch
theorem _root_.solution {pMain pCell pSetup pBuild pFill pRow pLinear pPowers pRank pOffset pErase : ℕ}
    (hmain : P[pMain]? = some (body pCell)) (hcell : P[pCell]? = some (LightZetaCell.body pSetup pOffset pErase pRank))
    (C : LightSubsetSetup.Procs P pSetup pBuild pFill pRow pLinear pPowers pRank)
    (hOffset : P[pOffset]? = some LightSubsetOffset.body) (hErase : P[pErase]? = some (LightMaskErase.body pErase))
    {μ : ℕ → ℤ} {L cut cardinal maskBase src dst work U d : ℕ} (masks : List ℕ) (a : Fin L) (f : Finset (Fin L) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hsrc : src + downsetCap L cut ≤ work) (hdst : dst + downsetCap L cut ≤ work)
    (hmasks : maskBase + masks.length ≤ work) (hsepSrc : Apart src (downsetCap L cut) dst (downsetCap L cut))
    (hsepMasks : Apart maskBase masks.length dst (downsetCap L cut))
    (hspace : work + LightPascal.tableSize L + (L + 1) ≤ lim.space)
    (hword : (((L + 1) * 2 ^ (L + 1) : ℕ) : ℤ) ≤ lim.word) (hvalueWord : 2 * (U : ℤ) ≤ lim.word)
    (hread : TableAt μ src cut f) (hvalues : ∀ T, T.card ≤ cut → |f T| ≤ U) (hseg : SegN μ maskBase masks)
    (hvalid : ∀ m ∈ masks, IsMask L cardinal m) (hcardinal : cardinal ≤ cut) (hd : d + L + 5 ≤ lim.depth) :
    Meets lim P pMain d [L, cardinal, masks.length, maskBase, a.val, src, dst, work] μ (time L masks.length)
      (fun _ μ' => TableAt μ' dst cut (values μ dst masks a f) ∧ KeptBut μ μ' work dst (downsetCap L cut)) :=
  by
  apply Meets.of_body hmain
  unfold body time
  refine
    Ends.for (Inv μ cut cardinal maskBase src dst work masks a f) masks.length (LightZetaCell.time L + 25) ?start ?round
      ?done ?bound (hT := by
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [] <;>
            first
            | omega
            | (ring_nf; omega)))
  case start =>
    refine ⟨0, μ, ?_, SameOn.refl, ?_⟩
    · simp [update_frame_setLocal]
      change
        frame [(L : ℤ), cardinal, masks.length, maskBase, a.val, src, dst, work, 0] =
          frame ([(L : ℤ), cardinal, masks.length, maskBase, a.val, src, dst, work, 0] ++ [0])
      exact (frame_append_zeros _ 1).symm
    · intro S hS
      simp [values]
  case round =>
    rintro j _ hj _ ⟨r, μ', rfl, hkept, hout⟩
    let m := masks[j]
    have hm : IsMask L cardinal m := hvalid m (List.getElem_mem hj)
    let S := decode L m
    have hScard : S.card = cardinal := by
      dsimp only [S]
      rw [decode_card hm.1, hm.2]
    have hSmask : subsetMask S = m := subsetMask_decode hm.1
    have hS : S.card ≤ cut := hScard.trans_le hcardinal
    have hrS := subsetRank_lt hS
    have hsource : TableAt μ' src cut f := by
      intro T hT
      have hr := subsetRank_lt hT
      exact (hkept _ ⟨by omega, by omega⟩).trans (hread T hT)
    have hmaskread : μ' (maskBase + j) = (m : ℤ) := by exact (hkept _ ⟨by omega, by omega⟩).trans (hseg.getElem hj)
    have hcall :=
      LightZetaCell.meets (d := d + 1) hcell C hOffset hErase S a f hw hsrc hdst hspace hword hvalueWord hsource hvalues
        hS (by omega)
    rw [hScard, hSmask] at hcall
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
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hmaskread,
              LightZetaCell.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hmaskread, LightZetaCell.time] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hmaskread, LightZetaCell.time] <;> omega)
      on_goal -1 => (rintro res μ'' ⟨hnew, hkeep⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    refine ⟨by simp, res, μ'', ?_, ?_, ?_⟩
    · simp [update_frame_setLocal]
    · intro i hi
      exact (hkeep i hi.1 (by omega)).trans (hkept i hi)
    · intro T hT
      have hrT := subsetRank_lt hT
      have htake : masks.take (j + 1) = masks.take j ++ [m] := by
        simpa only [m] using List.take_succ_eq_append_getElem (l := masks) hj
      by_cases heq : T = S
      · subst T
        rw [hnew]
        simp [values, htake, hSmask]
      · have hrne : dst + subsetRank T ≠ dst + subsetRank S :=
          by
          intro hh
          apply heq
          exact subsetRank_injective L (Nat.add_left_cancel hh)
        have hmne : subsetMask T ≠ m := by
          intro hh
          apply heq
          exact subsetMask_injective L (hh.trans hSmask.symm)
        rw [hkeep _ (by omega) hrne, hout T hT]
        simp only [values, htake, List.mem_append, List.mem_singleton, hmne, or_false]
  case done =>
    rintro _ _ ⟨r, μ', rfl, hkept, hout⟩
    exact ⟨by simpa only [List.take_length] using hout, hkept⟩
  case bound =>
    rintro j _ hj _ ⟨r, μ', rfl, _, _⟩
    ( (try have := _root_.Light.Std.space_le (by assumption))
      (try have := _root_.Light.Std.const_le (by assumption))
      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
end ThreeSum.LightZetaBatch
