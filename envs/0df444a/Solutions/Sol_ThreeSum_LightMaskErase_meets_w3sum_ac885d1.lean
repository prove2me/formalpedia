-- Prove2me | solution 1 for ThreeSum.LightMaskErase.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:14:07.024122+00:00
-- url     : https://prove2.me/submissions/955faab9-7ac9-4c28-8148-bee566ff7f59

import Definitions.Def_Submission_ThreeSum_MaskErase
import Definitions.Def_Submission_ThreeSum_LightSubsetAddress
import Definitions.Def_Submission_ThreeSum_LightMaskErase
import Theorems.Thm_Light_Ends_iteLast
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Definitions.Def_WeightedCache3SUM_Alias_88b09a412b2c33a9
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
set_option autoImplicit false
open ThreeSum ThreeSum.LightMaskErase
open Light ThreeSum.MaskErase ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightMaskErase
theorem _root_.solution {pErase W powers : ℕ} (hprog : P[pErase]? = some (body pErase)) (μ : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hspace : powers + (W + 1) ≤ lim.space)
    (hword : ((2 ^ (W + 1) : ℕ) : ℤ) ≤ lim.word) (hpowers : Powers μ powers W) :
    ∀ L a m : ℕ,
      L ≤ W →
        a ≤ W →
          m < 2 ^ L →
            ∀ d,
              d + L ≤ lim.depth →
                Meets lim P pErase d [L, a, m, W, powers] μ (time L) (fun r μ' => r = (eraseMask L a m : ℤ) ∧ μ' = μ) :=
  by
  have hpowW : ((2 ^ W : ℕ) : ℤ) ≤ lim.word :=
    by
    have h : (2 ^ W : ℕ) ≤ 2 ^ (W + 1) := Nat.pow_le_pow_right (by decide) (by omega)
    exact (by exact_mod_cast h : ((2 ^ W : ℕ) : ℤ) ≤ ((2 ^ (W + 1) : ℕ) : ℤ)).trans hword
  intro L
  induction L with
  | zero =>
    intro a m hL ha hm d hd
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
    intro a m hL ha hm d hd
    have hLW : L ≤ W := by omega
    have hpm := hpowers L hLW
    have hpow : (2 ^ L : ℕ) ≤ 2 ^ W := Nat.pow_le_pow_right (by decide) hLW
    have hpowZ : ((2 ^ L : ℕ) : ℤ) ≤ lim.word := by
      exact (by exact_mod_cast hpow : ((2 ^ L : ℕ) : ℤ) ≤ ((2 ^ W : ℕ) : ℤ)).trans hpowW
    have hpowN : (0 : ℤ) ≤ μ (powers + L) := by rw [hpm]; exact Int.natCast_nonneg _
    have hmW : m < 2 ^ W := hm.trans_le (Nat.pow_le_pow_right (by decide) hL)
    have hmZ : (m : ℤ) < ((2 ^ W : ℕ) : ℤ) := by exact_mod_cast hmW
    simp only [Nat.cast_pow, Nat.cast_ofNat] at hpm hpowZ hmZ hpowW
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
      have hchild := ih a m hLW ha hlo (d + 1) (by omega)
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
      exact ⟨by simpa [eraseMask, hlo] using hr, rfl⟩
    · have hhi : ¬m < 2 ^ L := by
        intro hh
        apply hhiZ
        rw [hpm]
        exact_mod_cast hh
      have hpLe : 2 ^ L ≤ m := Nat.le_of_not_gt hhi
      have hpLeZ : ((2 ^ L : ℕ) : ℤ) ≤ m := by exact_mod_cast hpLe
      have hrest : m - 2 ^ L < 2 ^ L := by rw [pow_succ] at hm; omega
      have hsub : (m : ℤ) - ((2 ^ L : ℕ) : ℤ) = ((m - 2 ^ L : ℕ) : ℤ) := by omega
      simp only [Nat.cast_pow, Nat.cast_ofNat] at hpLeZ hsub
      focus
        ((first
            | refine _root_.Light.Ends.seqSelf ?_
            | refine _root_.Light.Ends.skipLast ?_);
          repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_)
        refine _root_.Light.Ends.iteIffThen ((a : ℤ) = (L : ℤ)) (fun haZ => ?_) (fun hnaZ => ?_) ?_ ?_
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
      · have haL : a = L := by exact_mod_cast haZ
        focus
          ((first
              | refine _root_.Light.Ends.seqSelf ?_
              | refine _root_.Light.Ends.skipLast ?_);
            repeat
              with_unfolding_none
                first
                | refine _root_.Light.Ends.seqAssoc ?_
                | refine _root_.Light.Ends.skipThen ?_)
          refine _root_.Light.Ends.setToThen (m - 2 ^ L : ℕ) ?_ ?_ ?_
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
          on_goal -1 =>
            ( (try have := _root_.Light.Std.space_le (by assumption))
              (try have := _root_.Light.Std.const_le (by assumption))
              simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hpm, hsub, time] <;> omega)
          try with_unfolding_none refine _root_.Light.Ends.skip ?_
        exact ⟨by simp [eraseMask, hhi, haL], rfl⟩
      · have haL : a ≠ L := by exact_mod_cast hnaZ
        have hchild := ih a (m - 2 ^ L) hLW ha hrest (d + 1) (by omega)
        have hb := eraseMask_le (a := a) hrest
        have hs : 2 ^ L + eraseMask L a (m - 2 ^ L) ≤ m := by omega
        have hsZ : ((2 ^ L : ℕ) : ℤ) + (eraseMask L a (m - 2 ^ L) : ℤ) ≤ m := by exact_mod_cast hs
        simp only [Nat.cast_pow, Nat.cast_ofNat] at hsZ
        have heNonneg : (0 : ℤ) ≤ eraseMask L a (m - 2 ^ L) := Int.natCast_nonneg _
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
          refine _root_.Light.Ends.setToThen (2 ^ L + eraseMask L a (m - 2 ^ L) : ℕ) ?_ ?_ ?_
          on_goal -1 =>
            first
            | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                  _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hpm, hr, time]
                first
                | omega
                | (ring_nf; omega))
            | omega
            |
              (simp [hpm, hr, time] <;>
                  first
                  | omega
                  | (ring_nf; omega))
          on_goal -1 =>
            ( (try have := _root_.Light.Std.space_le (by assumption))
              (try have := _root_.Light.Std.const_le (by assumption))
              simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hpm, hr, time] <;> omega)
          try with_unfolding_none refine _root_.Light.Ends.skip ?_
        exact ⟨by simp [eraseMask, hhi, haL], rfl⟩
end ThreeSum.LightMaskErase
