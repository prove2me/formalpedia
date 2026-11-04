-- Prove2me | solution 1 for ThreeSum.LightLocalKeyRow.Procs.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:56:05.455122+00:00
-- url     : https://prove2.me/submissions/bcad171a-5e2d-4cdc-b9dd-6bf562c84e09

import Definitions.Def_Submission_ThreeSum_LightMaskHashes
import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_LightLocalKeyRow
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_fill_meets
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
import Definitions.Def_WeightedCache3SUM_Alias_a7357418fd94c5da
import Definitions.Def_WeightedCache3SUM_Alias_d061ef657958844a
import Definitions.Def_WeightedCache3SUM_Alias_aeb4de5e6b301b55
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
open ThreeSum ThreeSum.LightLocalKeyRow
open Light LightSubsetAddress
set_option maxHeartbeats 2400000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightLocalKeyRow
namespace Procs
theorem _root_.solution {pMain : ℕ} (S : Procs P pMain) {μ : ℕ → ℤ} {L masks n srcFalse srcTrue free U : ℕ}
    (mask wFalse wTrue : ℕ → ℕ) (hw : (lim.space : ℤ) ≤ lim.word) (hd : d + L + 2 ≤ lim.depth)
    (hspace : space free L n ≤ lim.space) (hmasks : masks + n ≤ free) (hfalse : srcFalse + L ≤ free)
    (htrue : srcTrue + L ≤ free) (hword : (word L U : ℤ) ≤ lim.word) (hmaskRead : ∀ i < n, μ (masks + i) = (mask i : ℤ))
    (hmaskLt : ∀ i < n, mask i < 2 ^ L) (hreadFalse : ∀ i < L, μ (srcFalse + i) = (wFalse i : ℤ))
    (hreadTrue : ∀ i < L, μ (srcTrue + i) = (wTrue i : ℤ)) (hboundFalse : ∀ i < L, wFalse i ≤ U)
    (hboundTrue : ∀ i < L, wTrue i ≤ U) :
    Meets lim P pMain d [L, masks, n, srcFalse, srcTrue, free] μ (time L n)
      (fun r ν =>
        r = ((free + L : ℕ) : ℤ) ∧
          (∀ i < n,
              ν (free + L + i) =
                (OneHotMask.eval wTrue (fun _ => 0) L (mask i) : ℤ) -
                  (OneHotMask.eval wFalse (fun _ => 0) L (mask i) : ℤ)) ∧
            Kept μ ν free) :=
  by
  let dst := free + L
  let tmp := dst + n
  let work := tmp + n
  have hs : work + (L + 1) ≤ lim.space := by dsimp [work, tmp, dst]; unfold space at hspace; omega
  have hhashWord : (LightOneHot.word L U : ℤ) ≤ lim.word := by
    exact (Int.ofNat_le.mpr (show LightOneHot.word L U ≤ word L U by unfold word; omega)).trans hword
  have hv : 2 * ((L * U : ℕ) : ℤ) ≤ lim.word :=
    by
    have hu : L * U ≤ LightOneHot.word L U := (Nat.mul_le_mul_right U (Nat.le_succ L)).trans (Nat.le_add_left _ _)
    have hn : 2 * (L * U) ≤ word L U := (Nat.mul_le_mul_left 2 hu).trans (Nat.le_add_right _ _)
    exact (by exact_mod_cast hn : 2 * ((L * U : ℕ) : ℤ) ≤ (word L U : ℤ)).trans hword
  have hzero : ∀ i < L, (0 : ℕ) ≤ U := by simp
  apply Meets.of_body S.main
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
    refine _root_.Light.Ends.setToThen (dst : ℕ) ?_ ?_ ?_
    on_goal -1 =>
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
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_)
    refine _root_.Light.Ends.setToThen (tmp : ℕ) ?_ ?_ ?_
    on_goal -1 =>
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
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_)
    refine _root_.Light.Ends.setToThen (work : ℕ) ?_ ?_ ?_
    on_goal -1 =>
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
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  have hf := fill_meets (d := d + 1) (μ := μ) (dst := free) (n := L) (x := 0) S.fill hw (by omega)
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
    | refine _root_.Light.Ends.callToThen (hf _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hf ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightMaskHashes.time, LightArray.linearTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightMaskHashes.time, LightArray.linearTime] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightMaskHashes.time, LightArray.linearTime] <;>
          omega)
    on_goal -1 => (rintro r₁ μ₁ ⟨hfilled, hkeep₁⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hz₁ (i : ℕ) (hi : i < L) : μ₁ (free + i) = (0 : ℤ) := by
    exact (hfilled i (by simpa using hi)).trans (List.getElem_replicate ..)
  have hm₁ (i : ℕ) (hi : i < n) : μ₁ (masks + i) = (mask i : ℤ) := (hkeep₁ _ (Or.inl (by omega))).trans (hmaskRead i hi)
  have ht₁ (i : ℕ) (hi : i < L) : μ₁ (srcTrue + i) = (wTrue i : ℤ) :=
    (hkeep₁ _ (Or.inl (by omega))).trans (hreadTrue i hi)
  have hfirst :=
    LightMaskHashes.meets (d := d + 1) (μ := μ₁) (L := L) (masks := masks) (dst := dst) (n := n) (src0 := srcTrue)
      (src1 := free) (work := work) (U := U) S.hashes S.powers S.hash mask wTrue (fun _ => 0) hw (by omega) hs
      (by dsimp [dst]; omega) (by dsimp [dst]; omega) le_rfl (by dsimp [work, tmp]; omega) hhashWord hm₁ hmaskLt ht₁ hz₁
      hboundTrue hzero
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
    | refine _root_.Light.Ends.callToThen (hfirst _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hfirst ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightMaskHashes.time, LightArray.linearTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightMaskHashes.time, LightArray.linearTime] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightMaskHashes.time, LightArray.linearTime] <;>
          omega)
    on_goal -1 => (rintro r₂ μ₂ ⟨hvaluesTrue, hpow₂, hkeep₂⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hm₂ (i : ℕ) (hi : i < n) : μ₂ (masks + i) = (mask i : ℤ) :=
    (hkeep₂ _ ⟨by dsimp [work, tmp, dst]; omega, Or.inl (by dsimp [dst]; omega)⟩).trans (hm₁ i hi)
  have hf₂ (i : ℕ) (hi : i < L) : μ₂ (srcFalse + i) = (wFalse i : ℤ) :=
    by
    rw [hkeep₂ _ ⟨by dsimp [work, tmp, dst]; omega, Or.inl (by dsimp [dst]; omega)⟩, hkeep₁ _ (Or.inl (by omega))]
    exact hreadFalse i hi
  have hz₂ (i : ℕ) (hi : i < L) : μ₂ (free + i) = (0 : ℤ) :=
    (hkeep₂ _ ⟨by dsimp [work, tmp, dst]; omega, Or.inl (by dsimp [dst]; omega)⟩).trans (hz₁ i hi)
  have hsecond :=
    LightMaskHashes.meets (d := d + 1) (μ := μ₂) (L := L) (masks := masks) (dst := tmp) (n := n) (src0 := srcFalse)
      (src1 := free) (work := work) (U := U) S.hashes S.powers S.hash mask wFalse (fun _ => 0) hw (by omega) hs
      (by dsimp [tmp, dst]; omega) (by dsimp [tmp, dst]; omega) (by dsimp [tmp, dst]; omega) le_rfl hhashWord hm₂
      hmaskLt hf₂ hz₂ hboundFalse hzero
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
    | refine _root_.Light.Ends.callToThen (hsecond _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hsecond ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightMaskHashes.time, LightArray.linearTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightMaskHashes.time, LightArray.linearTime] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightMaskHashes.time, LightArray.linearTime] <;>
          omega)
    on_goal -1 => (rintro r₃ μ₃ ⟨hvaluesFalse, hpow₃, hkeep₃⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have ht₃ (i : ℕ) (hi : i < n) : μ₃ (dst + i) = (OneHotMask.eval wTrue (fun _ => 0) L (mask i) : ℤ) :=
    (hkeep₃ _ ⟨by dsimp [work, tmp]; omega, Or.inl (by dsimp [tmp]; omega)⟩).trans (hvaluesTrue i hi)
  have hvalues : ∀ i < n, |μ₃ (dst + i)| ≤ ((L * U : ℕ) : ℤ) ∧ |μ₃ (tmp + i)| ≤ ((L * U : ℕ) : ℤ) :=
    by
    intro i hi
    rw [ht₃ i hi, hvaluesFalse i hi]
    simp only [Int.abs_natCast]
    exact
      ⟨Int.ofNat_le.mpr (OneHotMask.eval_le hboundTrue hzero), Int.ofNat_le.mpr (OneHotMask.eval_le hboundFalse hzero)⟩
  have hl :=
    LightArray.linear_bounded_meets (d := d + 1) (μ := μ₃) (srcA := dst) (srcB := tmp) (dst := dst) (n := n) (U :=
      L * U) (c := -1) S.linear hw (by omega) (by omega) (by omega) (Or.inl rfl)
      (Or.inr (Or.inr (by dsimp [tmp]; omega))) (by norm_num) hv hvalues
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
    | refine _root_.Light.Ends.callToThen (hl _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hl ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightMaskHashes.time, LightArray.linearTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightMaskHashes.time, LightArray.linearTime] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightMaskHashes.time, LightArray.linearTime] <;>
          omega)
    on_goal -1 => (rintro r₄ μ₄ ⟨hout, hkeep₄⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_)
    refine _root_.Light.Ends.setToThen (dst : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightMaskHashes.time, LightArray.linearTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightMaskHashes.time, LightArray.linearTime] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightMaskHashes.time, LightArray.linearTime] <;>
          omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  refine ⟨by simp [dst], ?_, ?_⟩
  · intro i hi
    change μ₄ (dst + i) = _
    rw [hout i hi, ht₃ i hi, hvaluesFalse i hi]
    ring
  · intro a ha
    change μ₄ a = μ a
    rw [hkeep₄ _ (Or.inl (by dsimp [dst]; omega)),
      hkeep₃ _ ⟨by dsimp [work, tmp, dst]; omega, Or.inl (by dsimp [tmp, dst]; omega)⟩,
      hkeep₂ _ ⟨by dsimp [work, tmp, dst]; omega, Or.inl (by dsimp [dst]; omega)⟩, hkeep₁ _ (Or.inl ha)]
end Procs
end ThreeSum.LightLocalKeyRow
