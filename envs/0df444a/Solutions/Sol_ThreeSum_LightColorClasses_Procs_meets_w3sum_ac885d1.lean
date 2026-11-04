-- Prove2me | solution 1 for ThreeSum.LightColorClasses.Procs.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:58:29.197609+00:00
-- url     : https://prove2.me/submissions/a7394ed0-6361-4d8f-b4f3-be7f1ec73bcf

import Definitions.Def_Submission_ThreeSum_LightColorArray
import Definitions.Def_Submission_ThreeSum_ColorClassLists
import Definitions.Def_Submission_ThreeSum_LightColorClasses
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_SegN_of_sameOutside
import Theorems.Thm_Light_SegN_read
import Theorems.Thm_Light_Seg_of_sameOutside
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_ColorClassLists_length_classList_le
import Theorems.Thm_ThreeSum_ColorClassLists_value_fin
import Theorems.Thm_ThreeSum_LightClassFilter_items_zero
import Definitions.Def_WeightedCache3SUM_Alias_98152438e5b788f3
import Definitions.Def_WeightedCache3SUM_Alias_ec1db2019105351a
import Theorems.Thm_ThreeSum_LightColorIndex_color_lt
import Definitions.Def_WeightedCache3SUM_Alias_5d83a00a3f301eb9
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
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
attribute [local simp] ThreeSum.ColorClassLists.value_fin
attribute [local simp] ThreeSum.LightClassFilter.items_zero
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
set_option autoImplicit false
open ThreeSum ThreeSum.LightColorClasses
open Light ColorClassLists
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightColorClasses
namespace Procs
theorem _root_.solution {pMain src n W colors dst0 dst1 dst2 work U : ℕ} {μ : ℕ → ℤ} (C : Procs P pMain)
    (p : Coloring.Parameter W) (x : Fin n → ℤ) (hw : (lim.space : ℤ) ≤ lim.word) (hn : n ≤ 2 ^ W)
    (hsrc : src + n ≤ colors) (hcolors : colors + n ≤ dst0) (h0 : dst0 + (n + 1) ≤ dst1) (h1 : dst1 + (n + 1) ≤ dst2)
    (h2 : dst2 + (n + 1) ≤ work) (hspace : work + (W + 1) ≤ lim.space) (hword : ((2 ^ (W + 1) : ℕ) : ℤ) ≤ lim.word)
    (hU : (U : ℤ) ≤ lim.word) (hd : d + W + 3 ≤ lim.depth) (hread : Seg μ src (List.ofFn x))
    (hbound : ∀ i, |x i| ≤ (U : ℤ)) :
    Meets lim P pMain d
      [src, n, W, p.1.1.val, p.1.2.val, (p.2 (false, false)).val, (p.2 (false, true)).val, (p.2 (true, false)).val,
        (p.2 (true, true)).val, colors, dst0, dst1, dst2, work]
      μ (time W n) (fun _ ν => Output p x μ ν colors dst0 dst1 dst2) :=
  by
  have hW := p.1.1.isLt
  have h3 : (3 : ℤ) ≤ lim.word :=
    by
    have hh : 2 ^ 2 ≤ 2 ^ (W + 1) := Nat.pow_le_pow_right (by decide) (by omega)
    have hh' : (4 : ℤ) ≤ ((2 ^ (W + 1) : ℕ) : ℤ) := by exact_mod_cast hh
    omega
  have read : ∀ i < n, μ (src + i) = value x i := by
    intro i hi
    have hh := hread i (by simpa using hi)
    simpa only [List.getElem_ofFn, ← value_fin x ⟨i, hi⟩] using hh
  have bound : ∀ i < n, |value x i| ≤ (U : ℤ) := by
    intro i hi
    simpa only [value, hi, dite_true] using hbound ⟨i, hi⟩
  have len0 := length_classList_le p x 0 1
  have len1 := length_classList_le p x 1 1
  apply Meets.of_body C.main
  unfold body time
  have hc :=
    LightColorArray.meets (d := d + 1) (n := n) (dst := colors) (work := work) C.colors C.powers C.color C.erase μ p hw
      hn (by omega) hspace hword (by omega)
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
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightColorArray.time, LightColorIndex.time,
            LightMaskErase.time, LightClassFilter.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightColorArray.time, LightColorIndex.time, LightMaskErase.time, LightClassFilter.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightColorArray.time, LightColorIndex.time,
            LightMaskErase.time, LightClassFilter.time] <;>
          omega)
    on_goal -1 => (rintro r ν₁ ⟨color₁, _, keep₁⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have read₁ : ∀ i < n, ν₁ (src + i) = value x i := by
    intro i hi
    exact (keep₁ _ ⟨by omega, Or.inl (by omega)⟩).trans (read i hi)
  have hf0 :=
    LightClassFilter.meets (d := d + 1) (μ := ν₁) (src := src) (colors := colors) (dst := dst0) (n := n) (want := 0)
      (scale := 1) (U := U) C.filter (value x) (LightColorIndex.color p) hw h3 (by omega) hcolors (by omega) (by decide)
      (by norm_num) hU read₁ color₁ (fun i _ => LightColorIndex.color_lt p i) bound
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
    | refine _root_.Light.Ends.callToThen (hf0 _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hf0 ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightColorArray.time, LightColorIndex.time,
            LightMaskErase.time, LightClassFilter.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightColorArray.time, LightColorIndex.time, LightMaskErase.time, LightClassFilter.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightColorArray.time, LightColorIndex.time,
            LightMaskErase.time, LightClassFilter.time] <;>
          omega)
    on_goal -1 => (rintro r ν₂ ⟨_, header0, values0, keep₂⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have read₂ : ∀ i < n, ν₂ (src + i) = value x i := by
    intro i hi
    exact (keep₂ _ (Or.inl (by omega))).trans (read₁ i hi)
  have color₂ : ∀ i < n, ν₂ (colors + i) = (LightColorIndex.color p i : ℤ) :=
    by
    intro i hi
    exact (keep₂ _ (Or.inl (by omega))).trans (color₁ i hi)
  have hf1 :=
    LightClassFilter.meets (d := d + 1) (μ := ν₂) (src := src) (colors := colors) (dst := dst1) (n := n) (want := 1)
      (scale := 1) (U := U) C.filter (value x) (LightColorIndex.color p) hw h3 (by omega) (by omega) (by omega)
      (by decide) (by norm_num) hU read₂ color₂ (fun i _ => LightColorIndex.color_lt p i) bound
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
    | refine _root_.Light.Ends.callToThen (hf1 _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hf1 ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightColorArray.time, LightColorIndex.time,
            LightMaskErase.time, LightClassFilter.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightColorArray.time, LightColorIndex.time, LightMaskErase.time, LightClassFilter.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightColorArray.time, LightColorIndex.time,
            LightMaskErase.time, LightClassFilter.time] <;>
          omega)
    on_goal -1 => (rintro r ν₃ ⟨_, header1, values1, keep₃⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have read₃ : ∀ i < n, ν₃ (src + i) = value x i := by
    intro i hi
    exact (keep₃ _ (Or.inl (by omega))).trans (read₂ i hi)
  have color₃ : ∀ i < n, ν₃ (colors + i) = (LightColorIndex.color p i : ℤ) :=
    by
    intro i hi
    exact (keep₃ _ (Or.inl (by omega))).trans (color₂ i hi)
  have hf2 :=
    LightClassFilter.meets (d := d + 1) (μ := ν₃) (src := src) (colors := colors) (dst := dst2) (n := n) (want := 2)
      (scale := -1) (U := U) C.filter (value x) (LightColorIndex.color p) hw h3 (by omega) (by omega) (by omega)
      (by decide) (by norm_num) hU read₃ color₃ (fun i _ => LightColorIndex.color_lt p i) bound
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
    | refine _root_.Light.Ends.callToThen (hf2 _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hf2 ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightColorArray.time, LightColorIndex.time,
            LightMaskErase.time, LightClassFilter.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightColorArray.time, LightColorIndex.time, LightMaskErase.time, LightClassFilter.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightColorArray.time, LightColorIndex.time,
            LightMaskErase.time, LightClassFilter.time] <;>
          omega)
    on_goal -1 => (rintro r ν₄ ⟨_, header2, values2, keep₄⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  refine ⟨?_, ?_, ?_, ?_, ?_, header2, values2, ?_⟩
  · intro i hi
    exact (keep₄ _ (Or.inl (by omega))).trans (color₃ i hi)
  · exact (keep₄ _ (Or.inl (by omega))).trans ((keep₃ _ (Or.inl (by omega))).trans header0)
  ·
    exact
      (values0.of_sameOutside keep₃
            (Or.inl (by change dst0 + 1 + (classList p x 0 1).length ≤ dst1; omega))).of_sameOutside
        keep₄ (Or.inl (by change dst0 + 1 + (classList p x 0 1).length ≤ dst2; omega))
  · exact (keep₄ _ (Or.inl (by omega))).trans header1
  · exact values1.of_sameOutside keep₄ (Or.inl (by change dst1 + 1 + (classList p x 1 1).length ≤ dst2; omega))
  · intro a ha
    exact
      (keep₄ _ (Or.inl (by omega))).trans
        ((keep₃ _ (Or.inl (by omega))).trans ((keep₂ _ (Or.inl (by omega))).trans (keep₁ _ ⟨by omega, Or.inl ha⟩)))
end Procs
end ThreeSum.LightColorClasses
