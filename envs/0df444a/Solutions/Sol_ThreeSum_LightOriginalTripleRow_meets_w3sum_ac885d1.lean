-- Prove2me | solution 1 for ThreeSum.LightOriginalTripleRow.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:07:12.681224+00:00
-- url     : https://prove2.me/submissions/05ee7848-d162-4d6e-9959-53473597ab9a

import Definitions.Def_Submission_ThreeSum_BruteTripleIndex
import Definitions.Def_Submission_ThreeSum_LightColorParameters
import Definitions.Def_Submission_ThreeSum_LightOriginalTripleRow
import Theorems.Thm_Light_Limits_Addr_abs_le
import Theorems.Thm_Light_Meets_mono_time
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_ColorClassLists_value_fin
import Theorems.Thm_ThreeSum_LightClassFilter_items_zero
import Definitions.Def_WeightedCache3SUM_Alias_98152438e5b788f3
import Definitions.Def_WeightedCache3SUM_Alias_5d83a00a3f301eb9
import Definitions.Def_WeightedCache3SUM_Alias_6cd6f72823a59258
import Theorems.Thm_ThreeSum_LightColorParameters_remainder
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab
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
open ThreeSum ThreeSum.LightOriginalTripleRow
open Light BruteTripleIndex
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightOriginalTripleRow
theorem _root_.solution {pMain pDivide src n t U d : ℕ} (x : Fin n → ℤ) (μ : ℕ → ℤ)
    (hp : P[pMain]? = some (body pDivide)) (hdivide : P[pDivide]? = some LightSmallDivide.body) (hn : 0 < n)
    (ht : t < n ^ 3) (hw : (lim.space : ℤ) ≤ lim.word) (hspace : src + n ≤ lim.space)
    (hword : (word n U : ℤ) ≤ lim.word) (hd : d < lim.depth) (hread : ∀ i : Fin n, μ (src + i.val) = x i)
    (hbound : ∀ i, |x i| ≤ (U : ℤ)) :
    Meets lim P pMain d [src, n, t] μ (time n)
      (fun result ν => (result = 0 ∨ result = 1) ∧ (result = 1 ↔ witness x hn ht) ∧ ν = μ) :=
  by
  have hb := bounds hn ht
  let a : Fin n := ⟨first n t, hb.1⟩
  let b : Fin n := ⟨second n t, hb.2.1⟩
  let c : Fin n := ⟨third n t, hb.2.2⟩
  have hwit : witness x hn ht ↔ a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ x a + x b + x c = 0 := Iff.rfl
  have hs (i : ℕ) (hi : i ≤ word n U) : (i : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hi).trans hword
  have hqBound : t / n < n * n := (Nat.div_lt_iff_lt_mul hn).mpr (by simpa only [pow_succ, pow_zero, one_mul] using ht)
  have hqle : t / n ≤ t := Nat.div_le_self _ _
  have hale : t / n / n ≤ t := (Nat.div_le_self _ _).trans hqle
  have hprodq : (t : ℤ) / (n : ℤ) * (n : ℤ) ≤ lim.word :=
    by
    have hh := (Nat.div_mul_le_self t n).trans (by unfold word; omega : t ≤ word n U)
    exact (by exact_mod_cast hh : (t : ℤ) / (n : ℤ) * (n : ℤ) ≤ (word n U : ℤ)).trans hword
  have hproda : (t : ℤ) / (n : ℤ) / (n : ℤ) * (n : ℤ) ≤ lim.word :=
    by
    have hh := (Nat.div_mul_le_self (t / n) n).trans (by unfold word; omega : t / n ≤ word n U)
    exact (by exact_mod_cast hh : (t : ℤ) / (n : ℤ) / (n : ℤ) * (n : ℤ) ≤ (word n U : ℤ)).trans hword
  have hprodq0 : (0 : ℤ) ≤ (t : ℤ) / (n : ℤ) * (n : ℤ) := by positivity
  have hproda0 : (0 : ℤ) ≤ (t : ℤ) / (n : ℤ) / (n : ℤ) * (n : ℤ) := by positivity
  have hj : (t : ℤ) / (n : ℤ) - (t : ℤ) / (n : ℤ) / (n : ℤ) * (n : ℤ) = (second n t : ℤ) := by
    simpa only [second, Int.natCast_ediv, Int.natCast_emod] using LightColorParameters.remainder (t / n) n
  have hk : (t : ℤ) - (t : ℤ) / (n : ℤ) * (n : ℤ) = (third n t : ℤ) := by
    simpa only [third, Int.natCast_ediv, Int.natCast_emod] using LightColorParameters.remainder t n
  have hA := abs_le.mp (hbound a)
  have hB := abs_le.mp (hbound b)
  have hC := abs_le.mp (hbound c)
  have hleft : |x a + x b| ≤ lim.word :=
    by
    have hh := hs (2 * U) (by unfold word; omega)
    push_cast at hh
    exact abs_le.mpr ⟨by omega, by omega⟩
  have hsum : |x a + x b + x c| ≤ lim.word :=
    by
    have hh := hs (3 * U) (by unfold word; omega)
    push_cast at hh
    exact abs_le.mpr ⟨by omega, by omega⟩
  have hleftSigned := abs_le.mp hleft
  have hsumSigned := abs_le.mp hsum
  have haWord := (hbound a).trans (hs U (by unfold word; omega))
  have hbWord := (hbound b).trans (hs U (by unfold word; omega))
  have hcWord := (hbound c).trans (hs U (by unfold word; omega))
  have haSigned := abs_le.mp haWord
  have hbSigned := abs_le.mp hbWord
  have hcSigned := abs_le.mp hcWord
  have hreadA := hread a
  have hreadB := hread b
  have hreadC := hread c
  apply Meets.of_body hp
  unfold body time
  have hq :=
    (LightSmallDivide.meets (d := d + 1) (a := t) (b := n) hdivide μ (hs _ (by unfold word; omega))).mono_time
      (show LightSmallDivide.time t n ≤ 20 * (n * n) + 40 by unfold LightSmallDivide.time; omega)
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
    | refine _root_.Light.Ends.callToThen (hq _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hq ?_ ?_ ?_ ?_
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
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
    on_goal -1 => (rintro q ν₁ ⟨hq, hν₁⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  subst ν₁
  have hqI : q = (t : ℤ) / (n : ℤ) := by simpa only [Int.natCast_ediv] using hq
  have hi :=
    (LightSmallDivide.meets (d := d + 1) (a := t / n) (b := n) hdivide μ (hs _ (by unfold word; omega))).mono_time
      (show LightSmallDivide.time (t / n) n ≤ 20 * n + 40 by unfold LightSmallDivide.time; dsimp [first] at hb; omega)
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
    | refine _root_.Light.Ends.callToThen (hi _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hi ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hq]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hq] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hq] <;> omega)
    on_goal -1 => (rintro i ν₂ ⟨hi, hν₂⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  subst ν₂
  have hiI : i = (t : ℤ) / (n : ℤ) / (n : ℤ) := by simpa only [Int.natCast_ediv] using hi
  have hi' : i = (first n t : ℤ) := hi
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_)
    refine _root_.Light.Ends.setToThen (second n t : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hqI, hiI, hj]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hqI, hiI, hj] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hqI, hiI, hj] <;> omega)
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
    refine _root_.Light.Ends.setToThen (third n t : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hqI, hk]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hqI, hk] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hqI, hk] <;> omega)
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
    refine _root_.Light.Ends.setToThen (x a) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hi', hreadA, a]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hi', hreadA, a] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hi', hreadA, a] <;> omega)
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
    refine _root_.Light.Ends.setToThen (x b) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hreadB, b]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hreadB, b] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hreadB, b] <;> omega)
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
    refine _root_.Light.Ends.setToThen (x c) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hreadC, c]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hreadC, c] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hreadC, c] <;> omega)
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
    refine _root_.Light.Ends.setToThen (x a + x b + x c) ?_ ?_ ?_
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
    refine _root_.Light.Ends.iteIffThen ((first n t : ℤ) = (second n t : ℤ)) (fun hAB => ?_) (fun hNAB => ?_) ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hi']
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hi'] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hi'] <;> omega)
    all_goals
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_
  · have hab : a = b := Fin.ext (by exact_mod_cast hAB)
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
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    exact ⟨by simp, by simp [hwit, hab], rfl⟩
  · have hab : a ≠ b := by intro hh; apply hNAB; exact_mod_cast congrArg Fin.val hh
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.iteIffThen ((first n t : ℤ) = (third n t : ℤ)) (fun hAC => ?_) (fun hNAC => ?_) ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hi']
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hi'] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hi'] <;> omega)
      all_goals
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_
    · have hac : a = c := Fin.ext (by exact_mod_cast hAC)
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
        try with_unfolding_none refine _root_.Light.Ends.skip ?_
      exact ⟨by simp, by simp [hwit, hac], rfl⟩
    · have hac : a ≠ c := by intro hh; apply hNAC; exact_mod_cast congrArg Fin.val hh
      focus
        ((first
            | refine _root_.Light.Ends.seqSelf ?_
            | refine _root_.Light.Ends.skipLast ?_);
          repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_)
        refine _root_.Light.Ends.iteIffThen ((second n t : ℤ) = (third n t : ℤ)) (fun hBC => ?_) (fun hNBC => ?_) ?_ ?_
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
      · have hbc : b = c := Fin.ext (by exact_mod_cast hBC)
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
          try with_unfolding_none refine _root_.Light.Ends.skip ?_
        exact ⟨by simp, by simp [hwit, hbc], rfl⟩
      · have hbc : b ≠ c := by intro hh; apply hNBC; exact_mod_cast congrArg Fin.val hh
        focus
          ((first
              | refine _root_.Light.Ends.seqSelf ?_
              | refine _root_.Light.Ends.skipLast ?_);
            repeat
              with_unfolding_none
                first
                | refine _root_.Light.Ends.seqAssoc ?_
                | refine _root_.Light.Ends.skipThen ?_)
          refine _root_.Light.Ends.iteIffThen (x a + x b + x c = 0) (fun hz => ?_) (fun hnz => ?_) ?_ ?_
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
        · focus
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
            try with_unfolding_none refine _root_.Light.Ends.skip ?_
          exact ⟨by simp, by simp [hwit, hab, hac, hbc, hz], rfl⟩
        · focus
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
            try with_unfolding_none refine _root_.Light.Ends.skip ?_
          exact ⟨by simp, by simp [hwit, hab, hac, hbc, hnz], rfl⟩
end ThreeSum.LightOriginalTripleRow
