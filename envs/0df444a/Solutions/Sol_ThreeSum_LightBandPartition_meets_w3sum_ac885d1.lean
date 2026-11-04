-- Prove2me | solution 1 for ThreeSum.LightBandPartition.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:18:20.248426+00:00
-- url     : https://prove2.me/submissions/9fcef290-4ff7-4d24-b1f3-1587517ce5e8

import Definitions.Def_Submission_ThreeSum_BandPartition
import Definitions.Def_Submission_ThreeSum_LightSmallDivide
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Copy
import Definitions.Def_Submission_ThreeSum_LightBandPartition
import Theorems.Thm_ThreeSum_LightBandPartition_lower_meets
import Definitions.Def_WeightedCache3SUM_Alias_8198b574e0c5bfd6
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_SameOn_refl
import Theorems.Thm_Light_SameOutside2_refl
import Theorems.Thm_Light_SameOutside_refl
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_BandPartition_size_le
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
set_option autoImplicit false
open ThreeSum ThreeSum.LightBandPartition
open Light ThreeSum.BandPartition
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightBandPartition
theorem _root_.solution {pMain pDivide pLower pUpper src dst n g d : ℕ}
    (hmain : P[pMain]? = some (body pDivide pLower pUpper)) (hdiv : P[pDivide]? = some LightSmallDivide.body)
    (hlower : P[pLower]? = some lowerBody) (hupper : P[pUpper]? = some upperBody) (μ : ℕ → ℤ) (f : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hg : 0 < g) (hsrc : src + n ≤ dst) (hspace : dst + 2 * n ≤ lim.space)
    (hword : ((n + g + 2 : ℕ) : ℤ) ≤ lim.word) (hread : ∀ i < n, μ (src + i) = f i) (hd : d + 1 ≤ lim.depth) :
    Meets lim P pMain d [src, n, g, dst] μ (time n g)
      (fun r μ' =>
        r = (size n g : ℤ) ∧
          (∀ i < size n g, μ' (dst + i) = f (start g i)) ∧
            (∀ i < size n g, μ' (dst + n + i) = f (stop n g i - 1)) ∧ SameOutside μ μ' dst (2 * n)) :=
  by
  have hm := size_le n g
  have hdv := Nat.div_le_self (n - 1) g
  apply Meets.of_body hmain
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
    refine _root_.Light.Ends.iteIffThen ((0 : ℤ) < (n : ℤ)) (fun hn => ?_) (fun hn => ?_) ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, lowerTime, upperTime, LightSmallDivide.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [lowerTime, upperTime, LightSmallDivide.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, lowerTime, upperTime, LightSmallDivide.time] <;>
          omega)
    all_goals
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_
  · have hnN : n ≠ 0 := by omega
    have hmval : size n g = (n - 1) / g + 1 := by simp [size, hnN]
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
      |
        refine
          _root_.Light.Ends.callToThen
            ((LightSmallDivide.meets (d := d + 1) (a := n - 1) (b := g) hdiv μ
                ((Int.ofNat_le.mpr (by omega : n - 1 + g + 2 ≤ n + g + 2)).trans hword))
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          _root_.Light.Ends.callToThen
            (LightSmallDivide.meets (d := d + 1) (a := n - 1) (b := g) hdiv μ
              ((Int.ofNat_le.mpr (by omega : n - 1 + g + 2 ≤ n + g + 2)).trans hword))
            ?_ ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, lowerTime,
              upperTime, LightSmallDivide.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [lowerTime, upperTime, LightSmallDivide.time] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, lowerTime, upperTime,
              LightSmallDivide.time] <;>
            omega)
      on_goal -1 => (rintro q μ₀ ⟨hq, hmem₀⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    subst μ₀
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.setToThen (size n g : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hmval, hq,
              lowerTime, upperTime, LightSmallDivide.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hmval, hq, lowerTime, upperTime, LightSmallDivide.time] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hmval, hq, lowerTime, upperTime,
              LightSmallDivide.time] <;>
            omega)
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
      refine _root_.Light.Ends.setToThen (dst + n : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, lowerTime,
              upperTime, LightSmallDivide.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [lowerTime, upperTime, LightSmallDivide.time] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, lowerTime, upperTime,
              LightSmallDivide.time] <;>
            omega)
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
      first
      |
        refine
          _root_.Light.Ends.callToThen ((lower_meets (d := d + 1) hlower μ f hw hg hsrc (by omega) hread) _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          _root_.Light.Ends.callToThen (lower_meets (d := d + 1) hlower μ f hw hg hsrc (by omega) hread) ?_ ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, lowerTime,
              upperTime, LightSmallDivide.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [lowerTime, upperTime, LightSmallDivide.time] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, lowerTime, upperTime,
              LightSmallDivide.time] <;>
            omega)
      on_goal -1 => (rintro unused μ₁ ⟨hlo, hkeep₁⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    have hread₁ : ∀ i < n, μ₁ (src + i) = f i := by
      intro i hi
      rw [hkeep₁ (src + i) (Or.inl (by omega))]
      exact hread i hi
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
      |
        refine
          _root_.Light.Ends.callToThen
            ((upper_meets (d := d + 1) (dst := dst + n) hupper μ₁ f hw hg (by omega) (by omega) hword hread₁) _
              (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          _root_.Light.Ends.callToThen
            (upper_meets (d := d + 1) (dst := dst + n) hupper μ₁ f hw hg (by omega) (by omega) hword hread₁) ?_ ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, lowerTime,
              upperTime, LightSmallDivide.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [lowerTime, upperTime, LightSmallDivide.time] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, lowerTime, upperTime,
              LightSmallDivide.time] <;>
            omega)
      on_goal -1 => (rintro unused μ₂ ⟨hhi, hkeep₂⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.setToThen (size n g : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, lowerTime,
              upperTime, LightSmallDivide.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [lowerTime, upperTime, LightSmallDivide.time] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, lowerTime, upperTime,
              LightSmallDivide.time] <;>
            omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    refine ⟨rfl, ?_, hhi, ?_⟩
    · intro i hi
      change μ₂ (dst + i) = _
      rw [hkeep₂ (dst + i) (Or.inl (by omega))]
      exact hlo i hi
    · intro a ha
      change μ₂ a = μ a
      rw [hkeep₂ a (by omega), hkeep₁ a (by omega)]
  · have hnN : n = 0 := by omega
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
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, lowerTime,
              upperTime, LightSmallDivide.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [lowerTime, upperTime, LightSmallDivide.time] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, lowerTime, upperTime,
              LightSmallDivide.time] <;>
            omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    refine ⟨by simp [size, hnN], ?_, ?_, SameOutside.refl⟩ <;> simp [size, hnN]
end ThreeSum.LightBandPartition
