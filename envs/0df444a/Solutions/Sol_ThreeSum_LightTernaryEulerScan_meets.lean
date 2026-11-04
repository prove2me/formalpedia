-- Prove2me | solution 1 for ThreeSum.LightTernaryEulerScan.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:38:25.040617+00:00
-- url     : https://prove2.me/submissions/cf11200d-f023-4f0b-a822-39c3244fa0ac

import Definitions.Def_Submission_ThreeSum_LightTernaryEulerRow
import Definitions.Def_Submission_ThreeSum_LightTernaryEulerScan
import Theorems.Thm_ThreeSum_LightTernaryEulerScan_stageValue_below
import Theorems.Thm_ThreeSum_LightTernaryEulerScan_Stored_next
import Theorems.Thm_Light_Ends_next
import Theorems.Thm_Light_Ends_pieceThen
import Theorems.Thm_Light_Ends_skip
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_fill_meets
import Theorems.Thm_Light_frame_append_zeros
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_LightTernaryEulerRow_fill_meets
import Theorems.Thm_ThreeSum_LightTernaryWeightedSum_sum_zero
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.LightTernaryWeightedSum.sum_zero
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryEulerScan
open Light
set_option maxHeartbeats 1800000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightTernaryEulerScan
theorem _root_.solution
    {pMain pFill pRow pSum pDivide pNaturalDivide N rows ws ks ranks vals current h pcount fr U V : ℕ}
    (hmain : P[pMain]? = some (body pFill)) (hfill : P[pFill]? = some (LightTernaryEulerRow.fillBody pRow))
    (hrow : P[pRow]? = some (LightTernaryEulerRow.body pSum pDivide))
    (hsum : P[pSum]? = some LightTernaryWeightedSum.body)
    (hdivide : P[pDivide]? = some (LightTernaryDivide.body pNaturalDivide))
    (hnatural : P[pNaturalDivide]? = some LightOutputDecodeDivide.body) (μ : ℕ → ℤ) (weights keys : ℕ → ℕ → ℕ)
    (g f : ℕ → ℤ) (rank : ℕ → ℕ) (F : Light.Emod.Pre lim (current - h) V fr) (hh : h ≤ current)
    (hws : ws + N * rows ≤ vals) (hks : ks + N * rows ≤ vals) (hranks : ranks + rows ≤ vals) (hvals : vals + rows ≤ fr)
    (hspace : pcount ≤ lim.space) (hrankRead : ∀ j < rows, μ (ranks + j) = (rank j : ℤ))
    (hweights : ∀ j < rows, ∀ i < N, μ (ws + N * j + i) = (weights j i : ℤ))
    (hkeys : ∀ j < rows, ∀ i < N, μ (ks + N * j + i) = (keys j i : ℤ))
    (hrange : ∀ j < rows, ∀ i < N, keys j i < pcount ∧ keys j i < fr)
    (hread : ∀ j < rows, rank j = current → ∀ i < N, μ (keys j i) = g (keys j i))
    (hweight : ∀ j < rows, ∀ i < N, weights j i ≤ 2)
    (hvalue : ∀ j < rows, rank j = current → ∀ i < N, |g (keys j i)| ≤ U)
    (hpre : ∀ j < rows, rank j = current → ∀ i < N, ∀ k < rows, rank k = current → keys j i ≠ vals + k)
    (hEuler :
      ∀ j < rows, rank j = current → LightTernaryWeightedSum.sum (weights j) (keys j) g N = (current - h : ℕ) * f j)
    (hV : 2 * (N + 1) * U ≤ V) (hd : d + 4 ≤ lim.depth)
    (hcontrols : ((N + rows + current + h + 20 : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P pMain d [N, rows, ws, ks, ranks, vals, current, h, pcount, fr] μ (time N rows V)
      (fun r ν => r = 0 ∧ Stored μ ν f rank vals current fr rows) :=
  by
  (obtain ⟨⟩ := _root_.id F)
  have hfr : fr ≤ lim.space := by omega
  have hwsWord : (ws : ℤ) ≤ lim.word := (Int.ofNat_le.mpr (by omega : ws ≤ lim.space)).trans F.space
  have hksWord : (ks : ℤ) ≤ lim.word := (Int.ofNat_le.mpr (by omega : ks ≤ lim.space)).trans F.space
  have hranksWord : (ranks : ℤ) ≤ lim.word := (Int.ofNat_le.mpr (by omega : ranks ≤ lim.space)).trans F.space
  have hvalsWord : (vals : ℤ) ≤ lim.word := (Int.ofNat_le.mpr (by omega : vals ≤ lim.space)).trans F.space
  have hcall {j : ℕ} (hj : j < rows) (ν : ℕ → ℤ) (H : Stored μ ν f rank vals current fr j) (hjrank : rank j = current) :
    Meets lim P pFill (d + 1)
      [(ws + N * j : ℕ), (ks + N * j : ℕ), (0 : ℕ), N, pcount, (current - h : ℕ), fr, (vals + j : ℕ)] ν
      (LightTernaryEulerRow.fillTime N V)
      (fun r ξ => r = f j ∧ ξ (vals + j) = f j ∧ ∀ a < fr, a ≠ vals + j → ξ a = ν a) :=
    by
    have hcoef (i : ℕ) (hi : i < N) : ws + N * j + i < vals := by nlinarith
    have hkey (i : ℕ) (hi : i < N) : ks + N * j + i < vals := by nlinarith
    have hpred (i : ℕ) (hi : i < N) : ν (keys j i) = g (keys j i) :=
      by
      rw [H _ (hrange j hj i hi).2]
      have hn : ¬(vals ≤ keys j i ∧ keys j i < vals + j ∧ rank (keys j i - vals) = current) :=
        by
        intro hc
        let k := keys j i - vals
        have hk : k < rows := by dsimp [k]; omega
        have he : keys j i = vals + k := by dsimp [k]; omega
        exact hpre j hj hjrank i hi k hk hc.2.2 he
      simp only [stageValue, if_neg hn]
      exact hread j hj hjrank i hi
    apply LightTernaryEulerRow.fill_meets hfill hrow hsum hdivide hnatural ν (weights j) (keys j) g F
    · nlinarith
    · nlinarith
    · simpa using hspace
    · intro i hi
      rw [H _ (by have hc := hcoef i hi; omega), stageValue_below μ f rank (hcoef i hi)]
      exact hweights j hj i hi
    · intro i hi
      rw [H _ (by have hc := hkey i hi; omega), stageValue_below μ f rank (hkey i hi)]
      exact hkeys j hj i hi
    · exact fun i hi => (hrange j hj i hi).1
    · simpa using hpred
    · exact hweight j hj
    · exact hvalue j hj hjrank
    · exact hV
    · exact hEuler j hj hjrank
    · omega
    · omega
  apply Meets.of_body hmain
  unfold body time
  refine
    Ends.pieceThen
      (Ends.for (T := rows * (LightTernaryEulerRow.fillTime N V + 150) + 20) (Q :=
        Inv μ f rank N rows ws ks ranks vals current h pcount fr rows)
        (Inv μ f rank N rows ws ks ranks vals current h pcount fr) rows (LightTernaryEulerRow.fillTime N V + 100) ?start
        ?round ?done ?bound (hT := by
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [] <;> first
              | omega
              | (ring_nf; omega))))
      ?after (hT := by
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [] <;> first
            | omega
            | (ring_nf; omega)))
  case start =>
    refine ⟨0, μ, ?_, ?_⟩
    ·
      simpa [update_frame_setLocal, setLocal] using
        congrArg (fun loc => (⟨loc, μ⟩ : State))
          (frame_append_zeros ([N, rows, ws, ks, ranks, vals, current, h, pcount, fr, 0] : List ℤ) 1).symm
    · intro a ha
      unfold stageValue
      rw [if_neg (by omega)]
  case round =>
    rintro j _ hj _ ⟨rval, ν, rfl, H⟩
    have hrspace : ranks + j < vals := by omega
    have hrread : ν (ranks + j) = (rank j : ℤ) :=
      by
      rw [H _ (by omega), stageValue_below μ f rank hrspace]
      exact hrankRead j hj
    have hwsN : ws + N * j + N ≤ vals := by nlinarith
    have hksN : ks + N * j + N ≤ vals := by nlinarith
    have hprodWord : ((N * j : ℕ) : ℤ) ≤ lim.word :=
      by
      have hs : N * j ≤ lim.space := by nlinarith
      exact (Int.ofNat_le.mpr hs).trans F.space
    have hdstWord : ((vals + j : ℕ) : ℤ) ≤ lim.word :=
      (Int.ofNat_le.mpr (by omega : vals + j ≤ lim.space)).trans F.space
    have hdiff : ((current - h : ℕ) : ℤ) = (current : ℤ) - (h : ℤ) := Nat.cast_sub hh
    unfold loopBody
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        (repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_))
      refine _root_.Light.Ends.iteIffThen (rank j = current) (fun hy => ?_) (fun hn => ?_) ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hrread]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hrread] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hrread] <;> omega)
      all_goals
        (repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_)
    · have hc := hcall hj ν H hy
      focus
        ((first
            | refine _root_.Light.Ends.seqSelf ?_
            | refine _root_.Light.Ends.skipLast ?_);
          (repeat
              with_unfolding_none
                first
                | refine _root_.Light.Ends.seqAssoc ?_
                | refine _root_.Light.Ends.skipThen ?_))
        first
        | refine _root_.Light.Ends.callToThen (hc _ (by omega)) ?_ ?_ ?_ ?_
        | refine _root_.Light.Ends.callToThen hc ?_ ?_ ?_ ?_
        on_goal -1 =>
          first
          | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hdiff,
                LightTernaryEulerRow.fillTime, LightTernaryEulerRow.time, LightTernaryWeightedSum.time,
                LightTernaryDivide.time]
              first
              | omega
              | (ring_nf; omega))
          | omega
          |
            (simp [hdiff, LightTernaryEulerRow.fillTime, LightTernaryEulerRow.time, LightTernaryWeightedSum.time,
                  LightTernaryDivide.time] <;> first
                | omega
                | (ring_nf; omega))
        on_goal -1 => omega
        on_goal -1 =>
          ( (try have := _root_.Light.Std.space_le (by assumption))
            (try have := _root_.Light.Std.const_le (by assumption))
            simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hdiff, LightTernaryEulerRow.fillTime,
                LightTernaryEulerRow.time, LightTernaryWeightedSum.time, LightTernaryDivide.time] <;> omega)
        on_goal -1 =>
          (rintro result ξ ⟨hresult, hwrite, hkeep⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
      refine ⟨by simp, result, ξ, ?_, H.next hy hwrite hkeep⟩
      simp [update_frame_setLocal]
    · apply Ends.skip
      refine ⟨by simp, rval, ν, ?_, H.skip hn⟩
      simp [update_frame_setLocal]
  case done => intro σ hcounter hshape; exact hshape
  case bound =>
    rintro j _ hj _ ⟨rval, ν, rfl, H⟩
    ( (try have := _root_.Light.Std.space_le (by assumption))
      (try have := _root_.Light.Std.const_le (by assumption))
      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
  case after =>
    rintro _ ⟨rval, ν, rfl, H⟩
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        (repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_))
      refine _root_.Light.Ends.setToThen 0 ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    exact ⟨rfl, H⟩
end ThreeSum.LightTernaryEulerScan
