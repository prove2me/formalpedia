-- Prove2me | solution 1 for ThreeSum.LightSourceBucketScatter.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:51:43.975208+00:00
-- url     : https://prove2.me/submissions/d08663c8-ef02-43e4-ac3c-61d92b86fee5

import Definitions.Def_Submission_ThreeSum_SourceBuckets
import Definitions.Def_Submission_ThreeSum_LightSourceBucketScatter
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
import Theorems.Thm_ThreeSum_LightHistogram_count_succ
import Theorems.Thm_ThreeSum_LightHistogram_count_zero
import Theorems.Thm_ThreeSum_SourceBuckets_offset_succ
import Theorems.Thm_ThreeSum_SourceBuckets_offset_zero
import Definitions.Def_WeightedCache3SUM_Alias_6a6a7bcd5722cb32
import Theorems.Thm_ThreeSum_SourceBuckets_position_lt
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.LightHistogram.count_zero
attribute [local simp] ThreeSum.SourceBuckets.offset_zero
set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceBucketScatter
open Light SourceBuckets LightHistogram
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightSourceBucketScatter
theorem _root_.solution {pMain : ℕ} (hmain : P[pMain]? = some body) {μ : ℕ → ℤ} {keys cursor flat N M : ℕ} (key : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hkeys : keys + N ≤ cursor) (hcursor : cursor + M ≤ flat)
    (hspace : flat + N ≤ lim.space) (hkey : ∀ i < N, key i < M) (hread : ∀ i < N, μ (keys + i) = (key i : ℤ))
    (hzero : ∀ r < M, μ (cursor + r) = (offset key N r : ℤ)) :
    Meets lim P pMain d [keys, cursor, flat, N, M] μ (time N)
      (fun _ ν =>
        (∀ i < N, ν (flat + position key N i) = (i : ℤ)) ∧
          (∀ r < M, ν (cursor + r) = (offset key N (r + 1) : ℤ)) ∧ SameOutside μ ν cursor (flat + N - cursor)) :=
  by
  apply Meets.of_body hmain
  unfold body time
  refine Ends.for (Inv μ key keys cursor flat N M) N 112 ?start ?round ?done ?bound
  case start =>
    refine ⟨0, 0, μ, ?_, ?_, ?_, SameOutside.refl⟩
    · exact congrArg (fun loc => (⟨loc, μ⟩ : State)) ((update_frame_setLocal _ _ _).trans (frame_append_zeros _ 2).symm)
    · simpa only [count_zero, Nat.add_zero] using hzero
    · intro j hj; omega
  case round =>
    rintro i _ hi _ ⟨k, q, ν, rfl, cursors, written, kept⟩
    have hki := hkey i hi
    have hread' : ν (keys + i) = (key i : ℤ) := (kept _ (Or.inl (by omega))).trans (hread i hi)
    have hcur : ν (cursor + key i) = (position key N i : ℤ) := cursors (key i) hki
    have hpos := position_lt hkey hi
    have hkiWord : (key i : ℤ) ≤ lim.word :=
      (by exact_mod_cast (show key i ≤ lim.space by omega) : (key i : ℤ) ≤ lim.space).trans hw
    have hposWord : (position key N i : ℤ) ≤ lim.word :=
      (by exact_mod_cast (show position key N i ≤ lim.space by omega) : (position key N i : ℤ) ≤ lim.space).trans hw
    have hnextWord : (position key N i + 1 : ℤ) ≤ lim.word :=
      (by exact_mod_cast (show position key N i + 1 ≤ lim.space by omega) :
            (position key N i + 1 : ℤ) ≤ lim.space).trans
        hw
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.setToThen (key i : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hread']
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hread'] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hread'] <;> omega)
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
      refine _root_.Light.Ends.setToThen (position key N i : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hcur]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hcur] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hcur] <;> omega)
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
      refine _root_.Light.Ends.storeToThen (flat + position key N i) (i : ℕ) ?_ ?_ ?_
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
      refine _root_.Light.Ends.storeToThen (cursor + key i) (position key N i + 1 : ℕ) ?_ ?_ ?_
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
    refine
      ⟨by simp, key i, position key N i,
        Function.update (Function.update ν (flat + position key N i) (i : ℤ)) (cursor + key i)
          (position key N i + 1 : ℕ),
        by simp [update_frame_setLocal], ?_, ?_, ?_⟩
    · intro r hr
      rw [count_succ]
      by_cases he : key i = r
      · subst r
        rw [Function.update_self]
        simp only [ite_true, position, Nat.cast_add, Nat.cast_one]
        ring
      · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), cursors r hr]
        simp only [he, ite_false, Nat.add_zero]
    · intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · have hne : position key N j ≠ position key N i := by
          intro he
          have hh := position_injective (show j < N by omega) hi he
          omega
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        exact written j hj
      · rw [Function.update_of_ne (by omega), Function.update_self]
    · intro a ha
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact kept a ha
  case done =>
    rintro _ _ ⟨k, q, ν, rfl, cursors, written, kept⟩
    refine ⟨written, ?_, kept⟩
    intro r hr
    rw [offset_succ]
    exact cursors r hr
  case bound =>
    rintro i _ hi _ ⟨k, q, ν, rfl, _, _, _⟩
    simp
end ThreeSum.LightSourceBucketScatter
