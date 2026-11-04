-- Prove2me | solution 1 for ThreeSum.LightOneHot.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:30:13.535058+00:00
-- url     : https://prove2.me/submissions/4e1a91c0-0c0a-466a-aae8-3f2091679829

import Definitions.Def_Submission_ThreeSum_OneHotMask
import Definitions.Def_Submission_ThreeSum_LightSubsetAddress
import Definitions.Def_Submission_ThreeSum_LightOneHot
import Theorems.Thm_Light_Ends_iteLast
import Theorems.Thm_Light_Meets_of_body
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
open ThreeSum ThreeSum.LightOneHot
open Light ThreeSum.OneHotMask ThreeSum.LightSubsetAddress
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightOneHot
theorem _root_.solution {pHash W powers src0 src1 U : ℕ} (hprog : P[pHash]? = some (body pHash)) (μ : ℕ → ℤ)
    (w0 w1 : ℕ → ℕ) (hw : (lim.space : ℤ) ≤ lim.word) (hspace : powers + (W + 1) ≤ lim.space)
    (hsrc0 : src0 + W ≤ lim.space) (hsrc1 : src1 + W ≤ lim.space) (hword : (word W U : ℤ) ≤ lim.word)
    (hpowers : Powers μ powers W) (hread0 : ∀ i < W, μ (src0 + i) = (w0 i : ℤ))
    (hread1 : ∀ i < W, μ (src1 + i) = (w1 i : ℤ)) (hbound0 : ∀ i < W, w0 i ≤ U) (hbound1 : ∀ i < W, w1 i ≤ U) :
    ∀ L m : ℕ,
      L ≤ W →
        m < 2 ^ L →
          ∀ d,
            d + L ≤ lim.depth →
              Meets lim P pHash d [L, m, W, powers, src0, src1] μ (time L)
                (fun r μ' => r = (OneHotMask.eval w0 w1 L m : ℤ) ∧ μ' = μ) :=
  by
  have hpBound : ((2 ^ (W + 1) : ℕ) : ℤ) ≤ lim.word :=
    by
    have hh : 2 ^ (W + 1) ≤ word W U := by unfold word; omega
    exact (by exact_mod_cast hh : ((2 ^ (W + 1) : ℕ) : ℤ) ≤ (word W U : ℤ)).trans hword
  have hvBound : ((W * U : ℕ) : ℤ) ≤ lim.word :=
    by
    have hh : W * U ≤ word W U := by
      calc
        W * U ≤ (W + 1) * U := Nat.mul_le_mul_right U (Nat.le_succ W)
        _ ≤ 2 ^ (W + 1) + (W + 1) * U := Nat.le_add_left _ _
    exact (by exact_mod_cast hh : ((W * U : ℕ) : ℤ) ≤ (word W U : ℤ)).trans hword
  intro L
  induction L with
  | zero =>
    intro m hL hm d hd
    apply Meets.of_body hprog
    unfold body time
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
    intro m hL hm d hd
    have hLW : L ≤ W := by omega
    have hLt : L < W := by omega
    have hpm := hpowers L hLW
    have h0 := hread0 L hLt
    have h1 := hread1 L hLt
    have h0U := hbound0 L hLt
    have h1U := hbound1 L hLt
    have h0Nonneg : (0 : ℤ) ≤ w0 L := Int.natCast_nonneg _
    have h1Nonneg : (0 : ℤ) ≤ w1 L := Int.natCast_nonneg _
    have hpLe : (2 ^ L : ℕ) ≤ 2 ^ (W + 1) := Nat.pow_le_pow_right (by decide) (by omega)
    have hpZ : ((2 ^ L : ℕ) : ℤ) ≤ lim.word := by
      exact (by exact_mod_cast hpLe : ((2 ^ L : ℕ) : ℤ) ≤ ((2 ^ (W + 1) : ℕ) : ℤ)).trans hpBound
    have hmLe : m < 2 ^ (W + 1) := hm.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
    have hmZ : (m : ℤ) < ((2 ^ (W + 1) : ℕ) : ℤ) := by exact_mod_cast hmLe
    have hpNonneg : (0 : ℤ) ≤ μ (powers + L) := by rw [hpm]; exact Int.natCast_nonneg _
    have h0' : ∀ i < L, w0 i ≤ U := fun i hi => hbound0 i (by omega)
    have h1' : ∀ i < L, w1 i ≤ U := fun i hi => hbound1 i (by omega)
    simp only [Nat.cast_pow, Nat.cast_ofNat] at hpm hpZ hmZ hpBound
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
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [time] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, time] <;> omega)
      all_goals
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_
    · have hlo : m < 2 ^ L := by rw [hpm] at hloZ; exact_mod_cast hloZ
      have hchild := ih m hLW hlo (d + 1) (by omega)
      have he := OneHotMask.eval_le (m := m) h0' h1'
      have hs : OneHotMask.eval w0 w1 L m + w0 L ≤ W * U := by nlinarith
      have hsZ : (OneHotMask.eval w0 w1 L m : ℤ) + (w0 L : ℤ) ≤ ((W * U : ℕ) : ℤ) := by exact_mod_cast hs
      have heNonneg : (0 : ℤ) ≤ OneHotMask.eval w0 w1 L m := Int.natCast_nonneg _
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
                _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, time]
              first
              | omega
              | (ring_nf; omega))
          | omega
          |
            (simp [time] <;>
                first
                | omega
                | (ring_nf; omega))
        on_goal -1 => omega
        on_goal -1 =>
          ( (try have := _root_.Light.Std.space_le (by assumption))
            (try have := _root_.Light.Std.const_le (by assumption))
            simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, time] <;> omega)
        on_goal -1 => (rintro res μ₁ ⟨hr, hmem⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
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
        refine _root_.Light.Ends.setToThen (OneHotMask.eval w0 w1 L m + w0 L : ℕ) ?_ ?_ ?_
        on_goal -1 =>
          first
          | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hr, h0, time]
              first
              | omega
              | (ring_nf; omega))
          | omega
          |
            (simp [hr, h0, time] <;>
                first
                | omega
                | (ring_nf; omega))
        on_goal -1 =>
          ( (try have := _root_.Light.Std.space_le (by assumption))
            (try have := _root_.Light.Std.const_le (by assumption))
            simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hr, h0, time] <;> omega)
        try with_unfolding_none refine _root_.Light.Ends.skip ?_
      exact ⟨by simp [OneHotMask.eval, hlo], rfl⟩
    · have hhi : ¬m < 2 ^ L := by
        intro hh
        apply hhiZ
        rw [hpm]
        exact_mod_cast hh
      have hpM : 2 ^ L ≤ m := Nat.le_of_not_gt hhi
      have hrest : m - 2 ^ L < 2 ^ L := by rw [pow_succ] at hm; omega
      have hsub : (m : ℤ) - ((2 ^ L : ℕ) : ℤ) = ((m - 2 ^ L : ℕ) : ℤ) := by omega
      simp only [Nat.cast_pow, Nat.cast_ofNat] at hsub
      have hchild := ih (m - 2 ^ L) hLW hrest (d + 1) (by omega)
      have he := OneHotMask.eval_le (m := m - 2 ^ L) h0' h1'
      have hs : OneHotMask.eval w0 w1 L (m - 2 ^ L) + w1 L ≤ W * U := by nlinarith
      have hsZ : (OneHotMask.eval w0 w1 L (m - 2 ^ L) : ℤ) + (w1 L : ℤ) ≤ ((W * U : ℕ) : ℤ) := by exact_mod_cast hs
      have heNonneg : (0 : ℤ) ≤ OneHotMask.eval w0 w1 L (m - 2 ^ L) := Int.natCast_nonneg _
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
                _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hpm, hsub, time]
              first
              | omega
              | (ring_nf; omega))
          | omega
          |
            (simp [hpm, hsub, time] <;>
                first
                | omega
                | (ring_nf; omega))
        on_goal -1 => omega
        on_goal -1 =>
          ( (try have := _root_.Light.Std.space_le (by assumption))
            (try have := _root_.Light.Std.const_le (by assumption))
            simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hpm, hsub, time] <;> omega)
        on_goal -1 => (rintro res μ₁ ⟨hr, hmem⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
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
        refine _root_.Light.Ends.setToThen (OneHotMask.eval w0 w1 L (m - 2 ^ L) + w1 L : ℕ) ?_ ?_ ?_
        on_goal -1 =>
          first
          | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hr, h1, time]
              first
              | omega
              | (ring_nf; omega))
          | omega
          |
            (simp [hr, h1, time] <;>
                first
                | omega
                | (ring_nf; omega))
        on_goal -1 =>
          ( (try have := _root_.Light.Std.space_le (by assumption))
            (try have := _root_.Light.Std.const_le (by assumption))
            simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hr, h1, time] <;> omega)
        try with_unfolding_none refine _root_.Light.Ends.skip ?_
      exact ⟨by simp [OneHotMask.eval, hhi], rfl⟩
end ThreeSum.LightOneHot
