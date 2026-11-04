-- Prove2me | solution 1 for ThreeSum.LightOriginalTripleScan.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:20:00.425026+00:00
-- url     : https://prove2.me/submissions/ecda0360-7bf6-4938-b211-74d6181508d6

import Definitions.Def_Submission_ThreeSum_LightOriginalTripleRow
import Definitions.Def_Submission_ThreeSum_LightOriginalTripleScan
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_BruteTripleIndex_hit_succ
import Theorems.Thm_ThreeSum_BruteTripleIndex_hit_zero
import Theorems.Thm_ThreeSum_ColorClassLists_value_fin
import Theorems.Thm_ThreeSum_LightClassFilter_items_zero
import Definitions.Def_WeightedCache3SUM_Alias_98152438e5b788f3
import Definitions.Def_WeightedCache3SUM_Alias_5d83a00a3f301eb9
import Definitions.Def_WeightedCache3SUM_Alias_6cd6f72823a59258
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_ec604c008ed4b1df
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
open ThreeSum ThreeSum.LightOriginalTripleScan
open Light BruteTripleIndex
set_option maxHeartbeats 1400000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightOriginalTripleScan
theorem _root_.solution {pMain pRow pDivide src n t U d : ℕ} (x : Fin n → ℤ) (μ : ℕ → ℤ)
    (hp : P[pMain]? = some (body pMain pRow)) (hrow : P[pRow]? = some (LightOriginalTripleRow.body pDivide))
    (hdivide : P[pDivide]? = some LightSmallDivide.body) (hn : 0 < n) (ht : t ≤ n ^ 3) (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : src + n ≤ lim.space) (hword : (LightOriginalTripleRow.word n U : ℤ) ≤ lim.word)
    (hd : d + t + 2 ≤ lim.depth) (hread : ∀ i : Fin n, μ (src + i.val) = x i) (hbound : ∀ i, |x i| ≤ (U : ℤ)) :
    Meets lim P pMain d [src, n, t] μ (time n t)
      (fun result ν => (result = 0 ∨ result = 1) ∧ (result = 1 ↔ Hit x hn t) ∧ ν = μ) :=
  by
  have htwo : (2 : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr
          (show (2 : ℕ) ≤ LightOriginalTripleRow.word n U by unfold LightOriginalTripleRow.word; omega)).trans
      hword
  have hcube : ((n ^ 3 : ℕ) : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (show n ^ 3 ≤ LightOriginalTripleRow.word n U by unfold LightOriginalTripleRow.word; omega)).trans
      hword
  induction t generalizing d with
  | zero =>
    apply Meets.of_body hp
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
      refine _root_.Light.Ends.iteIffThen ((0 : ℤ) < 0) (fun hbad => ?_) (fun hno => ?_) ?_ ?_
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
    · omega
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
      exact ⟨by simp, by simp [hit_zero], rfl⟩
  | succ t ih =>
    have ht' : t < n ^ 3 := by omega
    apply Meets.of_body hp
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
      refine _root_.Light.Ends.iteIffThen ((0 : ℤ) < ((t + 1 : ℕ) : ℤ)) (fun hyes => ?_) (fun hbad => ?_) ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil,
              LightOriginalTripleRow.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [LightOriginalTripleRow.time] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightOriginalTripleRow.time] <;> omega)
      all_goals
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_
    · have hrec := ih (d := d + 1) (by omega) (by omega)
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
        | refine _root_.Light.Ends.callToThen (hrec _ (by omega)) ?_ ?_ ?_ ?_
        | refine _root_.Light.Ends.callToThen hrec ?_ ?_ ?_ ?_
        on_goal -1 =>
          first
          | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, time,
                LightOriginalTripleRow.time]
              first
              | omega
              | (ring_nf; omega))
          | omega
          |
            (simp [time, LightOriginalTripleRow.time] <;>
                first
                | omega
                | (ring_nf; omega))
        on_goal -1 => omega
        on_goal -1 =>
          ( (try have := _root_.Light.Std.space_le (by assumption))
            (try have := _root_.Light.Std.const_le (by assumption))
            simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, time, LightOriginalTripleRow.time] <;>
              omega)
        on_goal -1 => (rintro prev ν₁ ⟨hprevBool, hprev, hν₁⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
      subst ν₁
      have hcall :=
        LightOriginalTripleRow.meets (d := d + 1) x μ hrow hdivide hn ht' hw hspace hword (by omega) hread hbound
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
                _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, time,
                LightOriginalTripleRow.time]
              first
              | omega
              | (ring_nf; omega))
          | omega
          |
            (simp [time, LightOriginalTripleRow.time] <;>
                first
                | omega
                | (ring_nf; omega))
        on_goal -1 => omega
        on_goal -1 =>
          ( (try have := _root_.Light.Std.space_le (by assumption))
            (try have := _root_.Light.Std.const_le (by assumption))
            simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, time, LightOriginalTripleRow.time] <;>
              omega)
        on_goal -1 =>
          (rintro found ν₂ ⟨hfoundBool, hfound, hν₂⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
      subst ν₂
      have hpRange : 0 ≤ prev ∧ prev ≤ 1 := by rcases hprevBool with hh | hh <;> omega
      have hfRange : 0 ≤ found ∧ found ≤ 1 := by rcases hfoundBool with hh | hh <;> omega
      have hsum : (0 : ℤ) < prev + found ↔ Hit x hn (t + 1) := by
        rw [hit_succ x hn ht', show (0 : ℤ) < prev + found ↔ prev = 1 ∨ found = 1 by omega, hprev, hfound]
      focus
        ((first
            | refine _root_.Light.Ends.seqSelf ?_
            | refine _root_.Light.Ends.skipLast ?_);
          repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_)
        refine _root_.Light.Ends.iteIffThen ((0 : ℤ) < prev + found) (fun hhit => ?_) (fun hmiss => ?_) ?_ ?_
        on_goal -1 =>
          first
          | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, time,
                LightOriginalTripleRow.time]
              first
              | omega
              | (ring_nf; omega))
          | omega
          |
            (simp [time, LightOriginalTripleRow.time] <;>
                first
                | omega
                | (ring_nf; omega))
        on_goal -1 =>
          ( (try have := _root_.Light.Std.space_le (by assumption))
            (try have := _root_.Light.Std.const_le (by assumption))
            simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, time, LightOriginalTripleRow.time] <;>
              omega)
        all_goals
          repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_
      · have hh := hsum.mp hhit
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
                  _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, time,
                  LightOriginalTripleRow.time]
                first
                | omega
                | (ring_nf; omega))
            | omega
            |
              (simp [time, LightOriginalTripleRow.time] <;>
                  first
                  | omega
                  | (ring_nf; omega))
          on_goal -1 =>
            ( (try have := _root_.Light.Std.space_le (by assumption))
              (try have := _root_.Light.Std.const_le (by assumption))
              simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, time, LightOriginalTripleRow.time] <;>
                omega)
          try with_unfolding_none refine _root_.Light.Ends.skip ?_
        exact ⟨by simp, by simpa using hh, rfl⟩
      · have hh : ¬Hit x hn (t + 1) := fun h => hmiss (hsum.mpr h)
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
                  _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, time,
                  LightOriginalTripleRow.time]
                first
                | omega
                | (ring_nf; omega))
            | omega
            |
              (simp [time, LightOriginalTripleRow.time] <;>
                  first
                  | omega
                  | (ring_nf; omega))
          on_goal -1 =>
            ( (try have := _root_.Light.Std.space_le (by assumption))
              (try have := _root_.Light.Std.const_le (by assumption))
              simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, time, LightOriginalTripleRow.time] <;>
                omega)
          try with_unfolding_none refine _root_.Light.Ends.skip ?_
        exact ⟨by simp, by simp [hh], rfl⟩
    · omega
end ThreeSum.LightOriginalTripleScan
