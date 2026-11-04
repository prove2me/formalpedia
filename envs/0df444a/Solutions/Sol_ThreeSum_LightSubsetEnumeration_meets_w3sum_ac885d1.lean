-- Prove2me | solution 1 for ThreeSum.LightSubsetEnumeration.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:30:33.715004+00:00
-- url     : https://prove2.me/submissions/85ea7c29-df3d-4571-bb93-9162577067fe

import Definitions.Def_Submission_ThreeSum_LightSubsetAddress
import Definitions.Def_Submission_ThreeSum_LightSubsetEnumeration
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_length
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_zero
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_empty
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_succ
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_work_pos
import Theorems.Thm_Light_Ends_iteLast
import Theorems.Thm_Light_LocalsBut_update
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_SameOn_refl
import Theorems.Thm_Light_SameOutside2_refl
import Theorems.Thm_Light_SameOutside_refl
import Theorems.Thm_Light_SegN_of_sameOutside
import Theorems.Thm_Light_Seg_of_sameOutside
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Definitions.Def_WeightedCache3SUM_Alias_04c57512725a2a98
import Definitions.Def_WeightedCache3SUM_Alias_3f3326597d4f4ccd
import Theorems.Thm_Light_toNat_natCast_add_natCast
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
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
attribute [local simp] ThreeSum.LightSubsetEnumeration.output_length
attribute [local simp] ThreeSum.LightSubsetEnumeration.output_zero
set_option autoImplicit false
open ThreeSum ThreeSum.LightSubsetEnumeration
open Light ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightSubsetEnumeration
theorem _root_.solution {pEnum W powers : ℕ} (hprog : P[pEnum]? = some (body pEnum)) (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : powers + (W + 1) ≤ lim.space) (hword : ((2 ^ (W + 1) : ℕ) : ℤ) ≤ lim.word) :
    ∀ L k pref dst : ℕ,
      ∀ μ : ℕ → ℤ,
        L ≤ W →
          k ≤ W + 1 →
            pref + 2 ^ L ≤ 2 ^ W →
              dst + L.choose k ≤ powers →
                Powers μ powers W →
                  ∀ d,
                    d + L ≤ lim.depth →
                      Meets lim P pEnum d [L, k, pref, dst, powers] μ (time L k)
                        (fun r μ' =>
                          r = (L.choose k : ℤ) ∧ Seg μ' dst (output L k pref) ∧ SameOutside μ μ' dst (L.choose k)) :=
  by
  have hpowWord : ((2 ^ W : ℕ) : ℤ) ≤ lim.word :=
    by
    have hn : (2 ^ W : ℕ) ≤ 2 ^ (W + 1) := Nat.pow_le_pow_right (by decide) (by omega)
    have hz : ((2 ^ W : ℕ) : ℤ) ≤ ((2 ^ (W + 1) : ℕ) : ℤ) := by exact_mod_cast hn
    exact hz.trans hword
  intro L
  induction L with
  | zero =>
    intro k pref dst μ hL hk hprefix hdst hpowers d hd
    have htime : 150 ≤ 150 * enumerationWork 0 k := Nat.mul_le_mul_left 150 (work_pos 0 k)
    have hprefNat : pref ≤ 2 ^ W := (Nat.le_add_right _ _).trans hprefix
    have hprefZ : (pref : ℤ) ≤ lim.word :=
      by
      have hz : (pref : ℤ) ≤ ((2 ^ W : ℕ) : ℤ) := by exact_mod_cast hprefNat
      exact hz.trans hpowWord
    cases k with
    | zero =>
      have hdspace : dst + 1 ≤ lim.space := by simpa using hdst.trans (by omega)
      apply Meets.of_body hprog
      unfold body time
      refine Ends.iteLast (fun _ => ?_) (fun h => False.elim (by simpa using h))
      focus
        ((first
            | refine _root_.Light.Ends.seqSelf ?_
            | refine _root_.Light.Ends.skipLast ?_);
          repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_)
        refine _root_.Light.Ends.storeToThen dst (pref : ℕ) ?_ ?_ ?_
        on_goal -1 =>
          first
          | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, enumerationWork]
              first
              | omega
              | (ring_nf; omega))
          | omega
          |
            (simp [enumerationWork] <;>
                first
                | omega
                | (ring_nf; omega))
        on_goal -1 =>
          ( (try have := _root_.Light.Std.space_le (by assumption))
            (try have := _root_.Light.Std.const_le (by assumption))
            simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, enumerationWork] <;> omega)
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
        refine _root_.Light.Ends.setToThen (1 : ℕ) ?_ ?_ ?_
        on_goal -1 =>
          first
          | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, enumerationWork]
              first
              | omega
              | (ring_nf; omega))
          | omega
          |
            (simp [enumerationWork] <;>
                first
                | omega
                | (ring_nf; omega))
        on_goal -1 =>
          ( (try have := _root_.Light.Std.space_le (by assumption))
            (try have := _root_.Light.Std.const_le (by assumption))
            simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, enumerationWork] <;> omega)
        try with_unfolding_none refine _root_.Light.Ends.skip ?_
      refine ⟨rfl, ?_, ?_⟩
      · simp [output_zero, seg_cons]
      · intro a ha
        simp only [Nat.choose_zero_right] at ha
        change Function.update μ dst (pref : ℤ) a = _
        exact Function.update_of_ne (by omega) _ _
    | succ k =>
      apply Meets.of_body hprog
      unfold body time
      refine Ends.iteLast (fun h => False.elim (by simp at h <;> omega)) (fun _ => ?_)
      refine Ends.iteLast (fun _ => ?_) (fun h => False.elim (by simpa using h))
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
          | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, enumerationWork]
              first
              | omega
              | (ring_nf; omega))
          | omega
          |
            (simp [enumerationWork] <;>
                first
                | omega
                | (ring_nf; omega))
        on_goal -1 =>
          ( (try have := _root_.Light.Std.space_le (by assumption))
            (try have := _root_.Light.Std.const_le (by assumption))
            simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, enumerationWork] <;> omega)
        try with_unfolding_none refine _root_.Light.Ends.skip ?_
      refine ⟨by simp, ?_, SameOutside.refl⟩
      rw [output_empty (L := 0) (k := k + 1) (by omega) pref]
      exact Seg.nil
  | succ L ih =>
    intro k pref dst μ hL hk hprefix hdst hpowers d hd
    have htime : 150 ≤ 150 * enumerationWork (L + 1) k := Nat.mul_le_mul_left 150 (work_pos (L + 1) k)
    have hLW : L ≤ W := by omega
    have hprefNat : pref ≤ 2 ^ W := (Nat.le_add_right _ _).trans hprefix
    have hprefZ : (pref : ℤ) ≤ lim.word :=
      by
      have hz : (pref : ℤ) ≤ ((2 ^ W : ℕ) : ℤ) := by exact_mod_cast hprefNat
      exact hz.trans hpowWord
    cases k with
    | zero =>
      have hdspace : dst + 1 ≤ lim.space := by simpa using hdst.trans (by omega)
      apply Meets.of_body hprog
      unfold body time
      refine Ends.iteLast (fun _ => ?_) (fun h => False.elim (by simpa using h))
      focus
        ((first
            | refine _root_.Light.Ends.seqSelf ?_
            | refine _root_.Light.Ends.skipLast ?_);
          repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_)
        refine _root_.Light.Ends.storeToThen dst (pref : ℕ) ?_ ?_ ?_
        on_goal -1 =>
          first
          | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, enumerationWork]
              first
              | omega
              | (ring_nf; omega))
          | omega
          |
            (simp [enumerationWork] <;>
                first
                | omega
                | (ring_nf; omega))
        on_goal -1 =>
          ( (try have := _root_.Light.Std.space_le (by assumption))
            (try have := _root_.Light.Std.const_le (by assumption))
            simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, enumerationWork] <;> omega)
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
        refine _root_.Light.Ends.setToThen (1 : ℕ) ?_ ?_ ?_
        on_goal -1 =>
          first
          | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, enumerationWork]
              first
              | omega
              | (ring_nf; omega))
          | omega
          |
            (simp [enumerationWork] <;>
                first
                | omega
                | (ring_nf; omega))
        on_goal -1 =>
          ( (try have := _root_.Light.Std.space_le (by assumption))
            (try have := _root_.Light.Std.const_le (by assumption))
            simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, enumerationWork] <;> omega)
        try with_unfolding_none refine _root_.Light.Ends.skip ?_
      refine ⟨by simp, ?_, ?_⟩
      · simp [output_zero, seg_cons]
      · intro a ha
        simp only [Nat.choose_zero_right] at ha
        change Function.update μ dst (pref : ℤ) a = _
        exact Function.update_of_ne (by omega) _ _
    | succ k =>
      apply Meets.of_body hprog
      unfold body time
      refine Ends.iteLast (fun h => False.elim (by simp at h <;> omega)) (fun _ => ?_)
      focus
        ((first
            | refine _root_.Light.Ends.seqSelf ?_
            | refine _root_.Light.Ends.skipLast ?_);
          repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_)
        refine
          _root_.Light.Ends.iteIffThen (((L + 1 : ℕ) : ℤ) < ((k + 1 : ℕ) : ℤ)) (fun hemptyZ => ?_) (fun hfullZ => ?_) ?_
            ?_
        on_goal -1 =>
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
                | (ring_nf; omega))
        on_goal -1 =>
          ( (try have := _root_.Light.Std.space_le (by assumption))
            (try have := _root_.Light.Std.const_le (by assumption))
            simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
        all_goals
          repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_
      · have hempty : L + 1 < k + 1 := by exact_mod_cast hemptyZ
        have hnot : ¬k + 1 ≤ L + 1 := by omega
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
            | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                  _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, enumerationWork,
                  hnot]
                first
                | omega
                | (ring_nf; omega))
            | omega
            |
              (simp [enumerationWork, hnot] <;>
                  first
                  | omega
                  | (ring_nf; omega))
          on_goal -1 =>
            ( (try have := _root_.Light.Std.space_le (by assumption))
              (try have := _root_.Light.Std.const_le (by assumption))
              simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, enumerationWork, hnot] <;> omega)
          try with_unfolding_none refine _root_.Light.Ends.skip ?_
        refine ⟨by simp [Nat.choose_eq_zero_of_lt hempty], ?_, SameOutside.refl⟩
        rw [output_empty hempty pref]
        exact Seg.nil
      · have hfull : k + 1 ≤ L + 1 := by exact_mod_cast (le_of_not_gt hfullZ)
        have hchoose : (L + 1).choose (k + 1) = L.choose (k + 1) + L.choose k := by
          rw [Nat.choose_succ_succ, Nat.add_comm]
        have hdst₀ : dst + L.choose (k + 1) ≤ powers := by omega
        have hdst₁ : dst + L.choose (k + 1) + L.choose k ≤ powers := by omega
        have hprefix₀ : pref + 2 ^ L ≤ 2 ^ W :=
          by
          have he : 2 ^ (L + 1) = 2 ^ L + 2 ^ L := by rw [pow_succ]; omega
          omega
        have hprefix₁ : pref + 2 ^ L + 2 ^ L ≤ 2 ^ W :=
          by
          have he : 2 ^ (L + 1) = 2 ^ L + 2 ^ L := by rw [pow_succ]; omega
          omega
        focus
          ((first
              | refine _root_.Light.Ends.seqSelf ?_
              | refine _root_.Light.Ends.skipLast ?_);
            repeat
              with_unfolding_none
                first
                | refine _root_.Light.Ends.seqAssoc ?_
                | refine _root_.Light.Ends.skipThen ?_)
          refine _root_.Light.Ends.setToThen (L : ℕ) ?_ ?_ ?_
          on_goal -1 =>
            first
            | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                  _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, enumerationWork,
                  hfull]
                first
                | omega
                | (ring_nf; omega))
            | omega
            |
              (simp [enumerationWork, hfull] <;>
                  first
                  | omega
                  | (ring_nf; omega))
          on_goal -1 =>
            ( (try have := _root_.Light.Std.space_le (by assumption))
              (try have := _root_.Light.Std.const_le (by assumption))
              simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, enumerationWork, hfull] <;> omega)
          try with_unfolding_none refine _root_.Light.Ends.skip ?_
        have hchild₀ := ih (k + 1) pref dst μ hLW hk hprefix₀ hdst₀ hpowers (d + 1) (by omega)
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
          | refine _root_.Light.Ends.callToThen (hchild₀ _ (by omega)) ?_ ?_ ?_ ?_
          | refine _root_.Light.Ends.callToThen hchild₀ ?_ ?_ ?_ ?_
          on_goal -1 =>
            first
            | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                  _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, time,
                  enumerationWork, hfull]
                first
                | omega
                | (ring_nf; omega))
            | omega
            |
              (simp [time, enumerationWork, hfull] <;>
                  first
                  | omega
                  | (ring_nf; omega))
          on_goal -1 => omega
          on_goal -1 =>
            ( (try have := _root_.Light.Std.space_le (by assumption))
              (try have := _root_.Light.Std.const_le (by assumption))
              simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, time, enumerationWork, hfull] <;> omega)
          on_goal -1 => (rintro n₀ μ₁ ⟨hn₀, hseg₀, hsame₀⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
        have hpowers₁ : Powers μ₁ powers W := by
          intro i hi
          rw [hsame₀ (powers + i) (Or.inr (by omega))]
          exact hpowers i hi
        have hpowerRead := hpowers₁ L hLW
        have hargPrefix : (pref : ℤ) + μ₁ (powers + L) = ((pref + 2 ^ L : ℕ) : ℤ) :=
          by
          rw [hpowerRead]
          push_cast
          rfl
        have hprefixArgBound : (pref : ℤ) + μ₁ (powers + L) ≤ lim.word :=
          by
          rw [hargPrefix]
          have hb : pref + 2 ^ L ≤ 2 ^ W := by omega
          have hz : ((pref + 2 ^ L : ℕ) : ℤ) ≤ ((2 ^ W : ℕ) : ℤ) := by exact_mod_cast hb
          exact hz.trans hpowWord
        have hreadNonneg : (0 : ℤ) ≤ μ₁ (powers + L) := by
          rw [hpowerRead]
          exact Int.natCast_nonneg _
        have hpowerEqInt : (2 : ℤ) ^ L = μ₁ (powers + L) := by simpa using hpowerRead.symm
        have hpowerIntNonneg : (0 : ℤ) ≤ (2 : ℤ) ^ L := by positivity
        have hprefixIntBound : (pref : ℤ) + (2 : ℤ) ^ L ≤ lim.word :=
          by
          rw [hpowerEqInt]
          exact hprefixArgBound
        have hchild₁ :=
          ih k (pref + 2 ^ L) (dst + L.choose (k + 1)) μ₁ hLW (by omega) hprefix₁ hdst₁ hpowers₁ (d + 1) (by omega)
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
          | refine _root_.Light.Ends.callToThen (hchild₁ _ (by omega)) ?_ ?_ ?_ ?_
          | refine _root_.Light.Ends.callToThen hchild₁ ?_ ?_ ?_ ?_
          on_goal -1 =>
            first
            | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                  _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, time,
                  enumerationWork, hfull, hn₀, hargPrefix]
                first
                | omega
                | (ring_nf; omega))
            | omega
            |
              (simp [time, enumerationWork, hfull, hn₀, hargPrefix] <;>
                  first
                  | omega
                  | (ring_nf; omega))
          on_goal -1 => omega
          on_goal -1 =>
            ( (try have := _root_.Light.Std.space_le (by assumption))
              (try have := _root_.Light.Std.const_le (by assumption))
              simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, time, enumerationWork, hfull, hn₀,
                  hargPrefix] <;>
                omega)
          on_goal -1 => (rintro n₁ μ₂ ⟨hn₁, hseg₁, hsame₁⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
        have htotalBound : ((L.choose (k + 1) + L.choose k : ℕ) : ℤ) ≤ lim.word :=
          by
          have hn : L.choose (k + 1) + L.choose k ≤ lim.space := by omega
          have hz : ((L.choose (k + 1) + L.choose k : ℕ) : ℤ) ≤ (lim.space : ℤ) := by exact_mod_cast hn
          exact hz.trans hw
        have hseg₀' : Seg μ₂ dst (output L (k + 1) pref) := hseg₀.of_sameOutside hsame₁ (Or.inl (by simp))
        focus
          ((first
              | refine _root_.Light.Ends.seqSelf ?_
              | refine _root_.Light.Ends.skipLast ?_);
            repeat
              with_unfolding_none
                first
                | refine _root_.Light.Ends.seqAssoc ?_
                | refine _root_.Light.Ends.skipThen ?_)
          refine _root_.Light.Ends.setToThen (L.choose (k + 1) + L.choose k : ℕ) ?_ ?_ ?_
          on_goal -1 =>
            first
            | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                  _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, time,
                  enumerationWork, hfull, hn₀, hn₁]
                first
                | omega
                | (ring_nf; omega))
            | omega
            |
              (simp [time, enumerationWork, hfull, hn₀, hn₁] <;>
                  first
                  | omega
                  | (ring_nf; omega))
          on_goal -1 =>
            ( (try have := _root_.Light.Std.space_le (by assumption))
              (try have := _root_.Light.Std.const_le (by assumption))
              simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, time, enumerationWork, hfull, hn₀,
                  hn₁] <;>
                omega)
          try with_unfolding_none refine _root_.Light.Ends.skip ?_
        refine ⟨by simpa [hchoose], ?_, ?_⟩
        · rw [output_succ hfull, seg_append, output_length]
          exact ⟨hseg₀', hseg₁⟩
        ·
          exact
            hsame₀.then hsame₁
              (fun a ha => by
                rw [hchoose] at ha
                constructor <;> omega)
end ThreeSum.LightSubsetEnumeration
