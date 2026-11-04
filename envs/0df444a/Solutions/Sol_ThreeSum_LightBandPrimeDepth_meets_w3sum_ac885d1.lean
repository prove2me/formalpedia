-- Prove2me | solution 1 for ThreeSum.LightBandPrimeDepth.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:59:38.987381+00:00
-- url     : https://prove2.me/submissions/62caeb4e-0902-4a07-8ac6-8fef1667428c

import Definitions.Def_Submission_ThreeSum_Scales
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Logs
import Definitions.Def_Submission_ThreeSum_LightBandPrimeDepth
import Theorems.Thm_Light_Ends_next
import Theorems.Thm_Light_Ends_whileBlock
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
set_option autoImplicit false
open ThreeSum ThreeSum.LightBandPrimeDepth
open Light
set_option maxHeartbeats 1200000
set_option maxRecDepth 8000
variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ} {R y : ℕ}
namespace ThreeSum.LightBandPrimeDepth
theorem _root_.solution {p : ℕ} (hp : P[p]? = some body) (hy : 0 < y) (hword : (word R y : ℤ) ≤ lim.word) :
    Meets lim P p d [R, y] μ (time R y) (fun result ν => result = (depth R y : ℤ) ∧ ν = μ) :=
  by
  have hbase : 1 < 4 * y := by omega
  have hltq := Nat.lt_pow_succ_log_self hbase (R / 4)
  simp only [Nat.succ_eq_add_one] at hltq
  have hlt : R < 4 * (4 * y) ^ (depth R y + 1) := by unfold depth; omega
  have hdepth : depth R y ≤ R := (Nat.log_le_self _ _).trans (Nat.div_le_self _ _)
  have hstart : (16 * y : ℕ) ≤ word R y := by unfold word; nlinarith
  have hR : (R : ℤ) ≤ lim.word := (Int.ofNat_le.mpr (by unfold word; omega : R ≤ word R y)).trans hword
  have hR1Word : (R : ℤ) + 1 ≤ lim.word := by
    exact_mod_cast (Int.ofNat_le.mpr (by unfold word; omega : R + 1 ≤ word R y)).trans hword
  have hstartWord : ((16 * y : ℕ) : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hstart).trans hword
  have hdepthWord : (depth R y : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hdepth).trans hR
  have hpower (i : ℕ) (hi : i ≤ depth R y) : 4 * (4 * y) ^ (i + 1) ≤ word R y :=
    by
    by_cases hz : R / 4 = 0
    · have hi0 : i = 0 := by simp only [depth, hz, Nat.log_zero_right] at hi; omega
      subst i
      simpa only [Nat.zero_add, pow_one, ← Nat.mul_assoc, show 4 * 4 = 16 by decide] using hstart
    · have hiLog : i ≤ Nat.log (4 * y) (R / 4) := hi
      have hp := (Nat.pow_le_pow_right hbase.le hiLog).trans (Nat.pow_log_le_self _ hz)
      have h4 : 4 * (4 * y) ^ i ≤ R := by omega
      have hm := Nat.mul_le_mul_right (4 * y) h4
      rw [pow_succ]
      unfold word
      nlinarith
  have hinit : 4 * (4 * y) ^ (0 + 1) = 16 * y := by ring
  have hfourWord : (4 : ℤ) * (y : ℤ) ≤ lim.word :=
    by
    have hh : 4 * y ≤ word R y := by omega
    exact_mod_cast (Int.ofNat_le.mpr hh).trans hword
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
    refine _root_.Light.Ends.setToThen (0 : ℕ) ?_ ?_ ?_
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
    refine _root_.Light.Ends.setToThen (16 * y : ℕ) ?_ ?_ ?_
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
  refine
    Ends.next _
      (Ends.whileBlock (T := 30 * depth R y + 10) (fun i σ => σ = ⟨frame [R, y, i, (4 * (4 * y) ^ (i + 1) : ℕ)], μ⟩)
        (depth R y) (by simp; rw [show (16 : ℤ) * (y : ℤ) = 4 * (4 * (y : ℤ)) by ring]) ?round ?done (by simp; omega))
      (hT := by
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
            | (ring_nf; omega)))
  case round =>
    rintro i _ hi rfl
    have hqne : R / 4 ≠ 0 := by
      intro hz
      simp [depth, hz] at hi
    have hiLog : i + 1 ≤ Nat.log (4 * y) (R / 4) := by change i < Nat.log (4 * y) (R / 4) at hi; omega
    have hpow : (4 * y) ^ (i + 1) ≤ R / 4 := (Nat.pow_le_pow_right hbase.le hiLog).trans (Nat.pow_log_le_self _ hqne)
    have hle : 4 * (4 * y) ^ (i + 1) ≤ R := by omega
    have hic : i + 1 ≤ R := by omega
    have hcurrentWord : ((4 * (4 * y) ^ (i + 1) : ℕ) : ℤ) ≤ lim.word :=
      (Int.ofNat_le.mpr (hpower i (by omega))).trans hword
    have hnext : 4 * y * (4 * (4 * y) ^ (i + 1)) ≤ word R y :=
      by
      have hh := Nat.mul_le_mul_left (4 * y) hle
      unfold word
      nlinarith
    have hnextZ : ((4 * y * (4 * (4 * y) ^ (i + 1)) : ℕ) : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hnext).trans hword
    have heq : 4 * (4 * y) ^ (i + 1 + 1) = 4 * y * (4 * (4 * y) ^ (i + 1)) := by ring
    rw [heq]
    generalize 4 * (4 * y) ^ (i + 1) = q at hle hnextZ hcurrentWord ⊢
    have hprodZ : (4 : ℤ) * (y : ℤ) * (q : ℤ) ≤ lim.word := by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hnextZ
    have hprodN : (0 : ℤ) ≤ (4 : ℤ) * (y : ℤ) * (q : ℤ) := by positivity
    exact
      ⟨by (
          (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega), by
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega), by
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega), by simp [update_frame_setLocal]⟩
  case done =>
    rintro _ rfl
    have hlastWord : ((4 * (4 * y) ^ (depth R y + 1) : ℕ) : ℤ) ≤ lim.word :=
      (Int.ofNat_le.mpr (hpower _ le_rfl)).trans hword
    generalize 4 * (4 * y) ^ (depth R y + 1) = q at hlt hlastWord ⊢
    refine
      ⟨by (
          (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega), by
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega), ?_⟩
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.setToThen (depth R y) ?_ ?_ ?_
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
end ThreeSum.LightBandPrimeDepth
