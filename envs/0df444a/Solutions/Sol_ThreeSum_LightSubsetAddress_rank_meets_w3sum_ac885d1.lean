-- Prove2me | solution 1 for ThreeSum.LightSubsetAddress.rank_meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:24:59.72532+00:00
-- url     : https://prove2.me/submissions/3a1b7f2a-15eb-4862-be93-c05560427f74

import Definitions.Def_Submission_ThreeSum_LightPascal
import Definitions.Def_Submission_ThreeSum_SubsetAddress
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_PowTable
import Definitions.Def_Submission_ThreeSum_LightSubsetAddress
import Theorems.Thm_ThreeSum_LightSubsetAddress_cell_offset_lt
import Theorems.Thm_Light_Ends_iteLast
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_high
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_le_width
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_low
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Definitions.Def_WeightedCache3SUM_Alias_a5ea34939403d75f
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
set_option autoImplicit false
open ThreeSum ThreeSum.LightSubsetAddress
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightSubsetAddress
theorem _root_.solution {pRank W table powers : ℕ} (hprog : P[pRank]? = some (rankBody pRank)) (μ : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (htspace : table + tableSize W ≤ lim.space)
    (hpspace : powers + (W + 1) ≤ lim.space) (hword : ((2 ^ (W + 1) : ℕ) : ℤ) ≤ lim.word) (htable : Table μ table W)
    (hpowers : Powers μ powers W) :
    ∀ L k m : ℕ,
      L ≤ W →
        IsMask L k m →
          ∀ d,
            d + L ≤ lim.depth →
              Meets lim P pRank d [L, k, m, W, table, powers] μ (rankTime L)
                (fun r μ' => r = (layerRank L k m : ℤ) ∧ μ' = μ) :=
  by
  have hpowW : ((2 ^ W : ℕ) : ℤ) ≤ lim.word :=
    by
    have hh : (2 ^ W : ℕ) ≤ 2 ^ (W + 1) := Nat.pow_le_pow_right (by decide) (by omega)
    have hhZ : ((2 ^ W : ℕ) : ℤ) ≤ ((2 ^ (W + 1) : ℕ) : ℤ) := by exact_mod_cast hh
    exact hhZ.trans hword
  have hwidth : W < lim.space := by omega
  intro L
  induction L with
  | zero =>
    intro k m hL hm d hd
    have hk : k = 0 := by have := hm.le_width; omega
    have hmask : m = 0 := by have := hm.1; simp only [pow_zero] at this; omega
    subst k
    subst m
    apply Meets.of_body hprog
    unfold rankBody rankTime
    refine Ends.iteLast (fun h => False.elim (by simpa using h)) (fun _ => ?_)
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
    exact ⟨rfl, rfl⟩
  | succ L ih =>
    intro k m hL hm d hd
    have hLW : L ≤ W := by omega
    have hkW : k ≤ W := hm.le_width.trans hL
    have hpowBound : (2 ^ L : ℕ) ≤ 2 ^ W := Nat.pow_le_pow_right (by decide) hLW
    have hmaskBound : m < 2 ^ W := hm.1.trans_le (Nat.pow_le_pow_right (by decide) hL)
    have hmaskZ : (m : ℤ) < ((2 ^ W : ℕ) : ℤ) := by exact_mod_cast hmaskBound
    have hpowZ : ((2 ^ L : ℕ) : ℤ) ≤ lim.word :=
      by
      have hh : ((2 ^ L : ℕ) : ℤ) ≤ ((2 ^ W : ℕ) : ℤ) := by exact_mod_cast hpowBound
      exact hh.trans hpowW
    have hpRead := hpowers L hLW
    have hpNonneg : (0 : ℤ) ≤ μ (powers + L) := by
      rw [hpRead]
      exact Int.natCast_nonneg _
    have htRead := htable L hLW k hkW
    have haddr : table + L * (W + 1) + k < lim.space :=
      by
      have hh := cell_offset_lt hLW hkW
      omega
    have hcast : (L : ℤ) * ((W : ℤ) + 1) = ((L * (W + 1) : ℕ) : ℤ) :=
      by
      push_cast
      rfl
    have haddrEq : ((table : ℤ) + (L : ℤ) * ((W : ℤ) + 1) + (k : ℤ)).toNat = table + L * (W + 1) + k :=
      by
      have he : (table : ℤ) + (L : ℤ) * ((W : ℤ) + 1) + (k : ℤ) = ((table + L * (W + 1) + k : ℕ) : ℤ) := by
        push_cast
        rfl
      rw [he, Int.toNat_natCast]
    have htReadZ : μ (((table : ℤ) + (L : ℤ) * ((W : ℤ) + 1) + (k : ℤ)).toNat) = (L.choose k : ℤ) := by
      rw [haddrEq, htRead]
    apply Meets.of_body hprog
    unfold rankBody rankTime
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
      refine _root_.Light.Ends.setToThen (L : ℕ) ?_ ?_ ?_
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
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.iteIffThen ((m : ℤ) < μ (powers + L)) (fun hloZ => ?_) (fun hhiZ => ?_) ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, rankTime]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [rankTime] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, rankTime] <;> omega)
      all_goals
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_
    · have hlo : m < 2 ^ L := by rw [hpRead] at hloZ; exact_mod_cast hloZ
      have hchild := ih k m hLW (hm.low hlo) (d + 1) (by omega)
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
        | refine _root_.Light.Ends.callToThen (hchild _ (by omega)) ?_ ?_ ?_ ?_
        | refine _root_.Light.Ends.callToThen hchild ?_ ?_ ?_ ?_
        on_goal -1 =>
          first
          | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, rankTime]
              first
              | omega
              | (ring_nf; omega))
          | omega
          |
            (simp [rankTime] <;>
                first
                | omega
                | (ring_nf; omega))
        on_goal -1 => omega
        on_goal -1 =>
          ( (try have := _root_.Light.Std.space_le (by assumption))
            (try have := _root_.Light.Std.const_le (by assumption))
            simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, rankTime] <;> omega)
        on_goal -1 => (rintro res μ₁ ⟨hres, hmem⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
      subst μ₁
      exact ⟨by simpa [layerRank, hlo] using hres, rfl⟩
    · have hhi : ¬m < 2 ^ L := by
        intro hh
        apply hhiZ
        rw [hpRead]
        exact_mod_cast hh
      obtain ⟨hkpos, hchildMask⟩ := hm.high (Nat.le_of_not_gt hhi)
      have hchild := ih (k - 1) (m - 2 ^ L) hLW hchildMask (d + 1) (by omega)
      have hrank :=
        (layerRank_lt hm).trans_le ((Nat.choose_le_two_pow (L + 1) k).trans (Nat.pow_le_pow_right (by decide) hL))
      rw [layerRank, if_neg hhi] at hrank
      have hrankZ : ((L.choose k + layerRank L (k - 1) (m - 2 ^ L) : ℕ) : ℤ) < ((2 ^ W : ℕ) : ℤ) := by
        exact_mod_cast hrank
      have hchooseNonneg : (0 : ℤ) ≤ (L.choose k : ℤ) := Int.natCast_nonneg _
      have hrestNonneg : (0 : ℤ) ≤ (layerRank L (k - 1) (m - 2 ^ L) : ℤ) := Int.natCast_nonneg _
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
        | refine _root_.Light.Ends.callToThen (hchild _ (by omega)) ?_ ?_ ?_ ?_
        | refine _root_.Light.Ends.callToThen hchild ?_ ?_ ?_ ?_
        on_goal -1 =>
          first
          | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, rankTime]
              first
              | omega
              | (ring_nf; omega))
          | omega
          |
            (simp [rankTime] <;>
                first
                | omega
                | (ring_nf; omega))
        on_goal -1 => omega
        on_goal -1 =>
          ( (try have := _root_.Light.Std.space_le (by assumption))
            (try have := _root_.Light.Std.const_le (by assumption))
            simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, rankTime] <;> omega)
        on_goal -1 => (rintro res μ₁ ⟨hres, hmem⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
      subst μ₁
      focus
        ((first
            | refine _root_.Light.Ends.seqSelf ?_
            | refine _root_.Light.Ends.skipLast ?_);
          repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_)
        refine _root_.Light.Ends.setToThen ((L.choose k + layerRank L (k - 1) (m - 2 ^ L) : ℕ)) ?_ ?_ ?_
        on_goal -1 =>
          first
          | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hres, htReadZ,
                rankTime, Nat.add_comm]
              first
              | omega
              | (ring_nf; omega))
          | omega
          |
            (simp [hres, htReadZ, rankTime, Nat.add_comm] <;>
                first
                | omega
                | (ring_nf; omega))
        on_goal -1 =>
          ( (try have := _root_.Light.Std.space_le (by assumption))
            (try have := _root_.Light.Std.const_le (by assumption))
            simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hres, htReadZ, rankTime, Nat.add_comm] <;>
              omega)
        try with_unfolding_none refine _root_.Light.Ends.skip ?_
      exact ⟨by simp [layerRank, hhi], rfl⟩
end ThreeSum.LightSubsetAddress
