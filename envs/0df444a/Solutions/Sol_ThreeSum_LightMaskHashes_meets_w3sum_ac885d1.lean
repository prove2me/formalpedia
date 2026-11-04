-- Prove2me | solution 1 for ThreeSum.LightMaskHashes.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:43:20.589019+00:00
-- url     : https://prove2.me/submissions/f7c6aa10-bc11-49ee-b38f-0af987d86ec2

import Definitions.Def_Submission_ThreeSum_LightOneHot
import Definitions.Def_Submission_ThreeSum_LightMaskHashes
import Theorems.Thm_Light_LocalsBut_update
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_powTable_meets
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Definitions.Def_WeightedCache3SUM_Alias_aeb4de5e6b301b55
import Theorems.Thm_ThreeSum_LightSubsetAddress_powers_of_segment
import Definitions.Def_WeightedCache3SUM_Alias_2f39c5fb289e3702
import Theorems.Thm_ThreeSum_OneHotMask_extend_fin
import Theorems.Thm_ThreeSum_OneHotMask_mem_natPositions
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
attribute [local simp] ThreeSum.OneHotMask.extend_fin
attribute [local simp] ThreeSum.OneHotMask.mem_natPositions
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
set_option autoImplicit false
open ThreeSum ThreeSum.LightMaskHashes
open Light LightSubsetAddress
set_option maxHeartbeats 1000000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightMaskHashes
theorem _root_.solution {pMain pPowers pHash : ℕ} (hmain : P[pMain]? = some (body pPowers pHash))
    (hpowers : P[pPowers]? = some powTableBody) (hhash : P[pHash]? = some (LightOneHot.body pHash)) {μ : ℕ → ℤ}
    {L masks dst n src0 src1 work U : ℕ} (mask w0 w1 : ℕ → ℕ) (hw : (lim.space : ℤ) ≤ lim.word)
    (hd : d + L + 1 ≤ lim.depth) (hspace : work + (L + 1) ≤ lim.space) (hmasks : masks + n ≤ dst)
    (hsrc0 : src0 + L ≤ dst) (hsrc1 : src1 + L ≤ dst) (hdst : dst + n ≤ work)
    (hword : (LightOneHot.word L U : ℤ) ≤ lim.word) (hmaskRead : ∀ i < n, μ (masks + i) = (mask i : ℤ))
    (hmaskLt : ∀ i < n, mask i < 2 ^ L) (hread0 : ∀ i < L, μ (src0 + i) = (w0 i : ℤ))
    (hread1 : ∀ i < L, μ (src1 + i) = (w1 i : ℤ)) (hbound0 : ∀ i < L, w0 i ≤ U) (hbound1 : ∀ i < L, w1 i ≤ U) :
    Meets lim P pMain d [L, masks, dst, n, src0, src1, work] μ (time L n)
      (fun _ μ' =>
        (∀ i < n, μ' (dst + i) = (OneHotMask.eval w0 w1 L (mask i) : ℤ)) ∧
          Powers μ' work L ∧ KeptBut μ μ' work dst n) :=
  by
  have hpWord : ((2 ^ (L + 1) : ℕ) : ℤ) ≤ lim.word :=
    by
    have hh : 2 ^ (L + 1) ≤ LightOneHot.word L U := by unfold LightOneHot.word; omega
    exact (Int.ofNat_le.mpr hh).trans hword
  have htwo : (2 : ℤ) ≤ lim.word :=
    by
    have hh : (2 ^ 1 : ℕ) ≤ 2 ^ (L + 1) := Nat.pow_le_pow_right (by decide) (by omega)
    exact (by exact_mod_cast hh : (2 : ℤ) ≤ ((2 ^ (L + 1) : ℕ) : ℤ)).trans hpWord
  have hvalWord : ((L * U : ℕ) : ℤ) ≤ lim.word :=
    by
    have hh : L * U ≤ LightOneHot.word L U := by
      unfold LightOneHot.word
      exact (Nat.mul_le_mul_right U (Nat.le_succ L)).trans (Nat.le_add_left _ _)
    exact (Int.ofNat_le.mpr hh).trans hword
  apply Meets.of_body hmain
  unfold body time
  have hp :=
    powTable_meets (d := d + 1) (μ := μ) (dst := work) (L := L + 1) (b := 2) hpowers hw hspace
      (by
        intro j hj
        exact (Int.ofNat_le.mpr (Nat.pow_le_pow_right (by decide) (by omega))).trans hpWord)
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
    | refine _root_.Light.Ends.callToThen (hp _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hp ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightOneHot.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightOneHot.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightOneHot.time] <;> omega)
    on_goal -1 => (rintro r μ₁ ⟨hpow, hkept⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hpow' : Powers μ₁ work L := powers_of_segment hpow
  unfold loopBody
  refine Ends.for (Inv μ mask w0 w1 L masks dst n src0 src1 work) n (LightOneHot.time L + 62) ?_ ?_ ?_ ?_
  · refine ⟨r, μ₁, ?_, ?_, hpow', ?_⟩
    · simp [update_frame_setLocal]
    · intro i hi
      omega
    · intro a ⟨ha, hout⟩
      exact hkept a (Or.inl ha)
  · rintro i _ hi _ ⟨r, μ', rfl, written, pows, kept⟩
    have hmr : μ' (masks + i) = (mask i : ℤ) := (kept _ ⟨by omega, Or.inl (by omega)⟩).trans (hmaskRead i hi)
    have h0 : ∀ j < L, μ' (src0 + j) = (w0 j : ℤ) := by
      intro j hj
      exact (kept _ ⟨by omega, Or.inl (by omega)⟩).trans (hread0 j hj)
    have h1 : ∀ j < L, μ' (src1 + j) = (w1 j : ℤ) := by
      intro j hj
      exact (kept _ ⟨by omega, Or.inl (by omega)⟩).trans (hread1 j hj)
    have he := OneHotMask.eval_le (m := mask i) hbound0 hbound1
    have heWord : (OneHotMask.eval w0 w1 L (mask i) : ℤ) ≤ lim.word := (Int.ofNat_le.mpr he).trans hvalWord
    have hh :=
      LightOneHot.meets (W := L) (powers := work) (src0 := src0) (src1 := src1) (U := U) hhash μ' w0 w1 hw hspace
        (by omega) (by omega) hword pows h0 h1 hbound0 hbound1 L (mask i) le_rfl (hmaskLt i hi) (d + 1) (by omega)
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
      | refine _root_.Light.Ends.callToThen (hh _ (by omega)) ?_ ?_ ?_ ?_
      | refine _root_.Light.Ends.callToThen hh ?_ ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hmr,
              LightOneHot.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hmr, LightOneHot.time] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hmr, LightOneHot.time] <;> omega)
      on_goal -1 => (rintro v μ₂ ⟨hv, hmem⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    subst μ₂
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.storeToThen (dst + i) (OneHotMask.eval w0 w1 L (mask i) : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hv,
              LightOneHot.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hv, LightOneHot.time] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hv, LightOneHot.time] <;> omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    refine
      ⟨by simp, v, Function.update μ' (dst + i) (OneHotMask.eval w0 w1 L (mask i) : ℤ), by simp [update_frame_setLocal],
        ?_, ?_, ?_⟩
    · intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [Function.update_of_ne (by omega)]
        exact written j hj
      · simp
    · intro j hj
      rw [Function.update_of_ne (by omega)]
      exact pows j hj
    · intro a ⟨ha, hout⟩
      rw [Function.update_of_ne (by omega)]
      exact kept a ⟨ha, hout⟩
  · rintro _ _ ⟨r, μ', rfl, written, pows, kept⟩
    exact ⟨written, pows, kept⟩
  · rintro i _ _ _ ⟨r, μ', rfl, _, _, _⟩
    simp
end ThreeSum.LightMaskHashes
