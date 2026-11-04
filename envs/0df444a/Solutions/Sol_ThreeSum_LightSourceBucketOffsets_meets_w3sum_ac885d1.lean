-- Prove2me | solution 1 for ThreeSum.LightSourceBucketOffsets.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:22:08.184198+00:00
-- url     : https://prove2.me/submissions/3a4d38e6-744b-4a05-ba55-74c5cc76b295

import Definitions.Def_Submission_ThreeSum_SourceBuckets
import Definitions.Def_Submission_ThreeSum_LightSourceBucketOffsets
import Theorems.Thm_Light_Ends_pieceThen
import Theorems.Thm_Light_LocalsBut_update
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_SameOn_refl
import Theorems.Thm_Light_SameOutside2_refl
import Theorems.Thm_Light_SameOutside_refl
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_LightHistogram_count_le
import Theorems.Thm_ThreeSum_LightHistogram_count_zero
import Theorems.Thm_ThreeSum_SourceBuckets_offset_le
import Theorems.Thm_ThreeSum_SourceBuckets_offset_succ
import Theorems.Thm_ThreeSum_SourceBuckets_offset_total
import Theorems.Thm_ThreeSum_SourceBuckets_offset_zero
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.LightHistogram.count_zero
attribute [local simp] ThreeSum.SourceBuckets.offset_zero
set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceBucketOffsets
open Light SourceBuckets LightHistogram
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightSourceBucketOffsets
theorem _root_.solution {pMain : ℕ} (hmain : P[pMain]? = some body) {μ : ℕ → ℤ} {hist offsets cursor M N : ℕ}
    (key : ℕ → ℕ) (hw : (lim.space : ℤ) ≤ lim.word) (hN : (N : ℤ) ≤ lim.word) (hhist : hist + M ≤ offsets)
    (hoffsets : offsets + M + 1 ≤ cursor) (hspace : cursor + M ≤ lim.space) (hkey : ∀ i < N, key i < M)
    (hread : ∀ r < M, μ (hist + r) = (count key r N : ℤ)) :
    Meets lim P pMain d [hist, offsets, cursor, M, N] μ (time M)
      (fun _ ν =>
        (∀ r ≤ M, ν (offsets + r) = (offset key N r : ℤ)) ∧
          (∀ r < M, ν (cursor + r) = (offset key N r : ℤ)) ∧ SameOutside μ ν offsets (cursor + M - offsets)) :=
  by
  have hval : (offset key N M : ℤ) ≤ lim.word := by
    rw [offset_total hkey]
    exact hN
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
    refine _root_.Light.Ends.setToThen 0 ?_ ?_ ?_
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
    Ends.pieceThen
      (Ends.for (Inv μ key hist offsets cursor M N) M 100 ?start ?round ?done ?bound (Q :=
        Inv μ key hist offsets cursor M N M) (T := 120 * M + 10) (hT := by
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
              | (ring_nf; omega))))
      ?finish
  case start =>
    refine ⟨μ, ?_, ?_, SameOutside.refl⟩
    · simp [update_frame_setLocal]
    · intro r hr; omega
  case round =>
    rintro i _ hi _ ⟨ν, rfl, written, kept⟩
    have hread' : ν (hist + i) = (count key i N : ℤ) := (kept _ (Or.inl (by omega))).trans (hread i hi)
    have ho := offset_le hkey (show i ≤ M by omega)
    have hn := offset_le hkey (show i + 1 ≤ M by omega)
    have hoWord := (Int.ofNat_le.mpr ho).trans hN
    have hnWord := (Int.ofNat_le.mpr hn).trans hN
    have hcWord := (Int.ofNat_le.mpr (count_le key i N)).trans hN
    have hsum : (offset key N i : ℤ) + (count key i N : ℤ) = (offset key N (i + 1) : ℤ) := by
      rw [offset_succ, Nat.cast_add]
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.storeToThen (offsets + i) (offset key N i : ℕ) ?_ ?_ ?_
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
      refine _root_.Light.Ends.storeToThen (cursor + i) (offset key N i : ℕ) ?_ ?_ ?_
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
    have hread'' :
      Function.update (Function.update ν (offsets + i) (offset key N i : ℤ)) (cursor + i) (offset key N i : ℤ)
          (hist + i) =
        (count key i N : ℤ) :=
      by rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), hread']
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.setToThen (offset key N (i + 1) : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hread'', hsum]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hread'', hsum] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hread'', hsum] <;> omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    refine
      ⟨by simp,
        Function.update (Function.update ν (offsets + i) (offset key N i : ℤ)) (cursor + i) (offset key N i : ℤ), by
        simp [update_frame_setLocal], ?_, ?_⟩
    · intro r hr
      rcases Nat.lt_succ_iff_lt_or_eq.mp hr with hr | rfl
      · constructor
        · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          exact (written r hr).1
        · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          exact (written r hr).2
      · constructor
        · rw [Function.update_of_ne (by omega), Function.update_self]
        · exact Function.update_self ..
    · intro a ha
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact kept a ha
  case done =>
    intro σ _ hs
    exact hs
  case bound =>
    rintro i _ hi _ ⟨ν, rfl, _, _⟩
    simp
  case finish =>
    rintro _ ⟨ν, rfl, written, kept⟩
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.storeToThen (offsets + M) (offset key N M : ℕ) ?_ ?_ ?_
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
    dsimp only
    refine ⟨?_, ?_, ?_⟩
    · intro r hr
      rcases lt_or_eq_of_le hr with hr | rfl
      · rw [Function.update_of_ne (by omega)]
        exact (written r hr).1
      · exact Function.update_self ..
    · intro r hr
      rw [Function.update_of_ne (by omega)]
      exact (written r hr).2
    · intro a ha
      rw [Function.update_of_ne (by omega)]
      exact kept a ha
end ThreeSum.LightSourceBucketOffsets
