-- Prove2me | solution 1 for ThreeSum.LightCoverScores.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:46:13.146891+00:00
-- url     : https://prove2.me/submissions/bf22fffb-d487-40dd-a5fd-8d48e193909f

import Definitions.Def_Submission_ThreeSum_LightBooleanDot
import Definitions.Def_Submission_ThreeSum_LightMinimum
import Definitions.Def_Submission_ThreeSum_LightCoverScores
import Theorems.Thm_Light_LocalsBut_update
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_SameOn_refl
import Theorems.Thm_Light_SameOutside2_refl
import Theorems.Thm_Light_SameOutside_refl
import Theorems.Thm_Light_frame_append_zeros
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_LightBooleanDot_dot_le
import Definitions.Def_WeightedCache3SUM_Alias_d7235e9f603abd3f
import Definitions.Def_WeightedCache3SUM_Alias_e1d95931a2ead3e4
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
set_option autoImplicit false
open ThreeSum ThreeSum.LightCoverScores
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightCoverScores
theorem _root_.solution {pMain pDot : ℕ} (hmain : P[pMain]? = some (body pDot))
    (hdot : P[pDot]? = some LightBooleanDot.body) {μ : ℕ → ℤ} {src activePtr dst rows cols : ℕ} (matrix : ℕ → ℕ → ℕ)
    (active : ℕ → ℕ) (hw : (lim.space : ℤ) ≤ lim.word) (hd : d < lim.depth) (hsrc : src + rows * cols ≤ dst)
    (hactive : activePtr + cols ≤ dst) (hspace : dst + rows ≤ lim.space)
    (hread : ∀ i < rows, ∀ j < cols, μ (src + i * cols + j) = (matrix i j : ℤ))
    (hreadActive : ∀ j < cols, μ (activePtr + j) = (active j : ℤ)) (hmatrix : ∀ i < rows, ∀ j < cols, matrix i j ≤ 1)
    (hactiveValue : ∀ j < cols, active j ≤ 1) (hword : (1 : ℤ) ≤ lim.word) :
    Meets lim P pMain d [src, activePtr, dst, cols, rows] μ (time rows cols)
      (fun _ μ' => (∀ i < rows, μ' (dst + i) = -(score matrix active cols i : ℤ)) ∧ SameOutside μ μ' dst rows) :=
  by
  apply Meets.of_body hmain
  unfold body time
  refine Ends.for (Inv μ matrix active src activePtr dst rows cols) rows (LightBooleanDot.time cols + 62) ?_ ?_ ?_ ?_
  · refine ⟨0, μ, ?_, ?_, SameOutside.refl⟩
    · exact congrArg (fun loc => (⟨loc, μ⟩ : State)) ((update_frame_setLocal _ _ _).trans (frame_append_zeros _ 1).symm)
    · intro j hj
      omega
  · rintro i _ hi _ ⟨v, μ', rfl, written, kept⟩
    have himul : (i + 1) * cols ≤ rows * cols := Nat.mul_le_mul_right cols (by omega)
    have hrow : src + i * cols + cols ≤ dst := by nlinarith
    have hrowRead : ∀ j < cols, μ' (src + i * cols + j) = (matrix i j : ℤ) :=
      by
      intro j hj
      rw [kept _ (by omega)]
      exact hread i hi j hj
    have hactRead : ∀ j < cols, μ' (activePtr + j) = (active j : ℤ) :=
      by
      intro j hj
      rw [kept _ (by omega)]
      exact hreadActive j hj
    have hrowSpace : src + i * cols + cols ≤ lim.space := by omega
    have hactiveSpace : activePtr + cols ≤ lim.space := by omega
    have hmul : ((i * cols : ℕ) : ℤ) ≤ lim.word :=
      by
      have hh : i * cols ≤ lim.space := by omega
      exact (by exact_mod_cast hh : ((i * cols : ℕ) : ℤ) ≤ lim.space).trans hw
    have haddr : ((src : ℤ) + (i : ℤ) * cols).toNat = src + i * cols := by
      rw [← Nat.cast_mul, ← Nat.cast_add, Int.toNat_natCast]
    have hcall :=
      LightBooleanDot.meets (d := d + 1) (μ := μ') (srcA := src + i * cols) (srcB := activePtr) (n := cols) hdot
        (matrix i) active hw hrowSpace hactiveSpace hrowRead hactRead (hmatrix i hi) hactiveValue hword
    have hs : score matrix active cols i ≤ cols :=
      LightBooleanDot.dot_le (matrix i) active (hmatrix i hi) hactiveValue le_rfl
    have hsZ : (score matrix active cols i : ℤ) ≤ lim.word :=
      by
      have hh : score matrix active cols i ≤ lim.space := by omega
      exact (by exact_mod_cast hh : (score matrix active cols i : ℤ) ≤ lim.space).trans hw
    have hsDotZ : (LightBooleanDot.dot (matrix i) active cols : ℤ) ≤ lim.word := hsZ
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
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, haddr,
              LightBooleanDot.time, score]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [haddr, LightBooleanDot.time, score] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, haddr, LightBooleanDot.time, score] <;> omega)
      on_goal -1 => (rintro r μ₁ ⟨hr, hmem⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
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
      refine _root_.Light.Ends.storeToThen (dst + i) (-(score matrix active cols i : ℤ)) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hr, score,
              LightBooleanDot.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hr, score, LightBooleanDot.time] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hr, score, LightBooleanDot.time] <;> omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    refine
      ⟨by simp, r, Function.update μ' (dst + i) (-(score matrix active cols i : ℤ)), by simp [update_frame_setLocal],
        ?_, ?_⟩
    · intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [Function.update_of_ne (by omega)]
        exact written j hj
      · simp
    · exact kept.update ⟨by omega, by omega⟩ _
  · rintro _ _ ⟨v, μ', rfl, written, kept⟩
    exact ⟨written, kept⟩
  · rintro i _ _ _ ⟨v, μ', rfl, _, _⟩
    simp
end ThreeSum.LightCoverScores
