-- Prove2me | solution 1 for ThreeSum.LightLocalKeys.Procs.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:08:25.7739+00:00
-- url     : https://prove2.me/submissions/e2e1dbdd-bec2-487b-b71a-2b4f3245c286

import Definitions.Def_Submission_ThreeSum_LightLocalKeyRow
import Definitions.Def_Submission_ThreeSum_LightLocalKeys
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_copy_meets
import Theorems.Thm_Light_frame_append_zeros
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Definitions.Def_WeightedCache3SUM_Alias_eb65baeba73fd57c
import Definitions.Def_WeightedCache3SUM_Alias_d061ef657958844a
import Definitions.Def_WeightedCache3SUM_Alias_aeb4de5e6b301b55
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
open ThreeSum ThreeSum.LightLocalKeys
open Light
set_option maxHeartbeats 2500000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightLocalKeys
namespace Procs
theorem _root_.solution {pMain : ℕ} (S : Procs P pMain) {μ : ℕ → ℤ} {L masks n maps rows dst free U : ℕ} (mask : ℕ → ℕ)
    (wFalse wTrue : ℕ → ℕ → ℕ) (hw : (lim.space : ℤ) ≤ lim.word) (hd : d + L + 3 ≤ lim.depth)
    (hspace : LightLocalKeyRow.space free L n ≤ lim.space) (hmasks : masks + n ≤ dst)
    (hmaps : maps + rows * (2 * L) ≤ dst) (hdst : dst + rows * n ≤ free) (hword : (word L U rows : ℤ) ≤ lim.word)
    (hmaskRead : ∀ i < n, μ (masks + i) = (mask i : ℤ)) (hmaskLt : ∀ i < n, mask i < 2 ^ L)
    (hreadFalse : ∀ j < rows, ∀ i < L, μ (maps + j * (2 * L) + i) = (wFalse j i : ℤ))
    (hreadTrue : ∀ j < rows, ∀ i < L, μ (maps + j * (2 * L) + L + i) = (wTrue j i : ℤ))
    (hboundFalse : ∀ j < rows, ∀ i < L, wFalse j i ≤ U) (hboundTrue : ∀ j < rows, ∀ i < L, wTrue j i ≤ U) :
    Meets lim P pMain d [L, masks, n, maps, rows, dst, free] μ (time L n rows)
      (fun _ ν =>
        (∀ j < rows,
            ∀ i < n,
              ν (dst + j * n + i) =
                (OneHotMask.eval (wTrue j) (fun _ => 0) L (mask i) : ℤ) -
                  (OneHotMask.eval (wFalse j) (fun _ => 0) L (mask i) : ℤ)) ∧
          Kept μ ν dst) :=
  by
  have hs : free + L + 2 * n + (L + 1) ≤ lim.space := hspace
  have hrowWord : (LightLocalKeyRow.word L U : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (show LightLocalKeyRow.word L U ≤ word L U rows by unfold word; omega)).trans hword
  have hrowsWord : (rows : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (show rows ≤ word L U rows by unfold word; omega)).trans hword
  have hwidthWord : (2 : ℤ) * L ≤ lim.word :=
    by
    have hh : 2 * L ≤ word L U rows := by unfold word; omega
    exact (by exact_mod_cast hh : (2 : ℤ) * L ≤ (word L U rows : ℤ)).trans hword
  have htwoWord : (2 : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (show 2 ≤ LightLocalKeyRow.word L U by unfold LightLocalKeyRow.word; omega)).trans hrowWord
  apply Meets.of_body S.main
  unfold body time
  refine
    Ends.for (Inv μ L masks n maps rows dst free mask wFalse wTrue) rows (LightLocalKeyRow.time L n + copyTime n + 120)
      ?_ ?_ ?_ ?_
  · refine ⟨0, 0, μ, ?_, ?_, by intro a ha; rfl⟩
    · exact congrArg (fun loc => (⟨loc, μ⟩ : State)) ((update_frame_setLocal _ _ _).trans (frame_append_zeros _ 2).symm)
    · intro j hj; omega
  · rintro j _ hj _ ⟨r, s, ν, rfl, written, kept⟩
    have hmj := Nat.mul_le_mul_right (2 * L) (show j + 1 ≤ rows by omega)
    have hdj := Nat.mul_le_mul_right n (show j + 1 ≤ rows by omega)
    simp only [Nat.add_mul, one_mul] at hmj hdj
    have hmProd : (j : ℤ) * (2 * L : ℤ) ≤ lim.word :=
      by
      have hh : j * (2 * L) ≤ lim.space := by omega
      exact (by exact_mod_cast hh : (j : ℤ) * (2 * L : ℤ) ≤ lim.space).trans hw
    have hmNonnegative : (0 : ℤ) ≤ (j : ℤ) * (2 * (L : ℤ)) := by positivity
    have hmAddr : (maps : ℤ) + (j : ℤ) * (2 * L : ℤ) + L ≤ lim.word :=
      by
      have hh : maps + j * (2 * L) + L ≤ lim.space := by omega
      exact (by exact_mod_cast hh : (maps : ℤ) + (j : ℤ) * (2 * L : ℤ) + L ≤ lim.space).trans hw
    have hdProd : (j : ℤ) * n ≤ lim.word :=
      by
      have hh : j * n ≤ lim.space := by omega
      exact (by exact_mod_cast hh : (j : ℤ) * n ≤ lim.space).trans hw
    have hdAddr : (dst : ℤ) + (j : ℤ) * n ≤ lim.word :=
      by
      have hh : dst + j * n ≤ lim.space := by omega
      exact (by exact_mod_cast hh : (dst : ℤ) + (j : ℤ) * n ≤ lim.space).trans hw
    have hmRead (i : ℕ) (hi : i < n) : ν (masks + i) = (mask i : ℤ) := (kept _ (by omega)).trans (hmaskRead i hi)
    have hfRead (i : ℕ) (hi : i < L) : ν (maps + j * (2 * L) + i) = (wFalse j i : ℤ) :=
      (kept _ (by omega)).trans (hreadFalse j hj i hi)
    have htRead (i : ℕ) (hi : i < L) : ν (maps + j * (2 * L) + L + i) = (wTrue j i : ℤ) :=
      (kept _ (by omega)).trans (hreadTrue j hj i hi)
    have hr :=
      S.row.meets (d := d + 1) (μ := ν) (L := L) (masks := masks) (n := n) (srcFalse := maps + j * (2 * L)) (srcTrue :=
        maps + j * (2 * L) + L) (free := free) (U := U) mask (wFalse j) (wTrue j) hw (by omega) hspace (by omega)
        (by omega) (by omega) hrowWord hmRead hmaskLt hfRead htRead (hboundFalse j hj) (hboundTrue j hj)
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
      | refine _root_.Light.Ends.callToThen (hr _ (by omega)) ?_ ?_ ?_ ?_
      | refine _root_.Light.Ends.callToThen hr ?_ ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil,
              LightLocalKeyRow.time, LightMaskHashes.time, LightArray.linearTime]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [LightLocalKeyRow.time, LightMaskHashes.time, LightArray.linearTime] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightLocalKeyRow.time, LightMaskHashes.time,
              LightArray.linearTime] <;>
            omega)
      on_goal -1 => (rintro row μ₁ ⟨hrowPtr, hrow, hkeep₁⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    have hc :=
      copy_meets (d := d + 1) (μ := μ₁) (src := free + L) (dst := dst + j * n) (n := n) S.copy hw (by omega) (by omega)
        (Or.inr (by omega))
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
      | refine _root_.Light.Ends.callToThen (hc _ (by omega)) ?_ ?_ ?_ ?_
      | refine _root_.Light.Ends.callToThen hc ?_ ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hrowPtr,
              LightLocalKeyRow.time, LightMaskHashes.time, LightArray.linearTime]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hrowPtr, LightLocalKeyRow.time, LightMaskHashes.time, LightArray.linearTime] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hrowPtr, LightLocalKeyRow.time,
              LightMaskHashes.time, LightArray.linearTime] <;>
            omega)
      on_goal -1 => (rintro copied μ₂ ⟨hcopy, hkeep₂⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    refine ⟨by simp, row, copied, μ₂, by simp [update_frame_setLocal], ?_, ?_⟩
    · intro k hk i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
      · have hki := Nat.mul_le_mul_right n (show k + 1 ≤ j by omega)
        simp only [Nat.add_mul, one_mul] at hki
        rw [hkeep₂ _ (Or.inl (by omega)), hkeep₁ _ (by omega)]
        exact written k hk i hi
      · rw [hcopy i hi, hrow i hi]
    · intro a ha
      rw [hkeep₂ _ (Or.inl (by omega)), hkeep₁ _ (by omega)]
      exact kept a ha
  · rintro _ _ ⟨r, s, ν, rfl, written, kept⟩
    exact ⟨written, kept⟩
  · rintro j _ hj _ ⟨r, s, ν, rfl, _, _⟩
    ( (try have := _root_.Light.Std.space_le (by assumption))
      (try have := _root_.Light.Std.const_le (by assumption))
      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
end Procs
end ThreeSum.LightLocalKeys
