-- Prove2me | solution 1 for ThreeSum.LightTernaryEulerMemo.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:45:35.110441+00:00
-- url     : https://prove2.me/submissions/a17abdb8-d8d2-4da2-8444-f9a2e00da3f8

import Definitions.Def_Submission_ThreeSum_LightTernaryEulerScan
import Definitions.Def_Submission_ThreeSum_LightTernaryEulerMemo
import Theorems.Thm_ThreeSum_LightTernaryEulerMemo_Ready_next
import Theorems.Thm_Light_Ends_next
import Theorems.Thm_Light_Ends_pieceThen
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
import Definitions.Def_WeightedCache3SUM_Alias_3252ff1ef14149f2
import Definitions.Def_WeightedCache3SUM_Alias_9a4576158068ee52
import Theorems.Thm_ThreeSum_LightTernaryDivide_meets
import Theorems.Thm_ThreeSum_LightTernaryEulerRow_meets
import Theorems.Thm_ThreeSum_LightTernaryEulerScan_Stored_next
import Theorems.Thm_ThreeSum_LightTernaryEulerScan_meets
import Theorems.Thm_ThreeSum_LightTernaryWeightedSum_sum_zero
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.LightTernaryWeightedSum.sum_zero
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryEulerMemo
open Light
set_option maxHeartbeats 1800000
set_option maxRecDepth 12000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightTernaryEulerMemo
theorem _root_.solution
    {pMain pScan pFill pRow pSum pDivide pNaturalDivide N rows ws ks ranks vals T h maxRank pcount fr U V : ℕ}
    (hmain : P[pMain]? = some (body pScan)) (hscan : P[pScan]? = some (LightTernaryEulerScan.body pFill))
    (hfill : P[pFill]? = some (LightTernaryEulerRow.fillBody pRow))
    (hrow : P[pRow]? = some (LightTernaryEulerRow.body pSum pDivide))
    (hsum : P[pSum]? = some LightTernaryWeightedSum.body)
    (hdivide : P[pDivide]? = some (LightTernaryDivide.body pNaturalDivide))
    (hnatural : P[pNaturalDivide]? = some LightOutputDecodeDivide.body) (μ : ℕ → ℤ) (weights keys : ℕ → ℕ → ℕ)
    (g f : ℕ → ℤ) (rank : ℕ → ℕ)
    (F : ∀ current, T < current → current ≤ maxRank → Light.Emod.Pre lim (current - h) V fr) (hT : T ≤ maxRank)
    (hh : h ≤ T) (hws : ws + N * rows ≤ vals) (hks : ks + N * rows ≤ vals) (hranks : ranks + rows ≤ vals)
    (hvals : vals + rows ≤ fr) (hspace : pcount ≤ lim.space) (hrankRead : ∀ j < rows, μ (ranks + j) = (rank j : ℤ))
    (hrankRange : ∀ j < rows, T < rank j ∧ rank j ≤ maxRank)
    (hweights : ∀ j < rows, ∀ i < N, μ (ws + N * j + i) = (weights j i : ℤ))
    (hkeys : ∀ j < rows, ∀ i < N, μ (ks + N * j + i) = (keys j i : ℤ))
    (hrange : ∀ j < rows, ∀ i < N, keys j i < pcount ∧ keys j i < fr)
    (hbank : ∀ j < rows, ∀ i < N, keys j i < vals → μ (keys j i) = g (keys j i))
    (hmemo : ∀ j < rows, g (vals + j) = f j) (hweight : ∀ j < rows, ∀ i < N, weights j i ≤ 2)
    (hvalue : ∀ j < rows, ∀ i < N, |g (keys j i)| ≤ U)
    (hpre : ∀ j < rows, ∀ i < N, keys j i < vals ∨ ∃ k < rows, keys j i = vals + k ∧ rank k < rank j)
    (hEuler : ∀ j < rows, LightTernaryWeightedSum.sum (weights j) (keys j) g N = (rank j - h : ℕ) * f j)
    (hV : 2 * (N + 1) * U ≤ V) (hd : d + 5 ≤ lim.depth) (hword : ((N + rows + maxRank + h + 20 : ℕ) : ℤ) ≤ lim.word)
    (hw : (lim.space : ℤ) ≤ lim.word) (hfr : fr ≤ lim.space) :
    Meets lim P pMain d [N, rows, ws, ks, ranks, vals, T, h, maxRank, pcount, fr] μ (time N rows (maxRank - T) V)
      (fun r ν => r = 0 ∧ Kept μ ν vals ∧ ∀ j < rows, ν (vals + j) = f j) :=
  by
  have hcall {stage : ℕ} (hstage : stage < maxRank - T) (ν : ℕ → ℤ) (H : Ready μ ν f rank vals rows T stage) :
    Meets lim P pScan (d + 1) [N, rows, ws, ks, ranks, vals, (T + stage + 1 : ℕ), h, pcount, fr] ν
      (LightTernaryEulerScan.time N rows V)
      (fun r ξ => r = 0 ∧ LightTernaryEulerScan.Stored ν ξ f rank vals (T + stage + 1) fr rows) :=
    by
    have hc : T + stage + 1 ≤ maxRank := by omega
    have hmeta {a : ℕ} (ha : a < vals) : ν a = μ a := H.1 a ha
    apply
      LightTernaryEulerScan.meets hscan hfill hrow hsum hdivide hnatural ν weights keys g f rank
        (F (T + stage + 1) (by omega) hc)
    · omega
    · exact hws
    · exact hks
    · exact hranks
    · exact hvals
    · exact hspace
    · intro j hj
      rw [hmeta (by omega)]
      exact hrankRead j hj
    · intro j hj i hi
      have ha : ws + N * j + i < vals := by nlinarith
      rw [hmeta ha]
      exact hweights j hj i hi
    · intro j hj i hi
      have ha : ks + N * j + i < vals := by nlinarith
      rw [hmeta ha]
      exact hkeys j hj i hi
    · exact hrange
    · intro j hj hjrank i hi
      rcases hpre j hj i hi with hb | ⟨k, hk, he, hr⟩
      · rw [hmeta hb]
        exact hbank j hj i hi hb
      · rw [he, H.2 k hk (by omega), hmemo k hk]
    · exact hweight
    · intro j hj _
      exact hvalue j hj
    · intro j hj hjrank i hi k hk hkr he
      rcases hpre j hj i hi with hb | ⟨l, hl, hel, hr⟩
      · omega
      · have heq : k = l := by omega
        subst l
        omega
    · intro j hj hjrank
      simpa only [hjrank] using hEuler j hj
    · exact hV
    · omega
    · have hb : N + rows + (T + stage + 1) + h + 20 ≤ N + rows + maxRank + h + 20 := by omega
      exact (Int.ofNat_le.mpr hb).trans hword
  apply Meets.of_body hmain
  unfold body time
  refine
    Ends.pieceThen
      (Ends.for (T := (maxRank - T) * (LightTernaryEulerScan.time N rows V + 150) + 20) (Q :=
        Inv μ f rank N rows ws ks ranks vals T h maxRank pcount fr (maxRank - T))
        (Inv μ f rank N rows ws ks ranks vals T h maxRank pcount fr) (maxRank - T)
        (LightTernaryEulerScan.time N rows V + 100) ?start ?round ?done ?bound (hT := by
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
          (frame_append_zeros ([N, rows, ws, ks, ranks, vals, T, h, maxRank, pcount, fr, 0] : List ℤ) 1).symm
    · refine ⟨SameOn.refl, ?_⟩
      intro j hj hr
      have hmin := (hrankRange j hj).1
      omega
  case round =>
    rintro stage _ hstage _ ⟨rval, ν, rfl, H⟩
    have hcurrent : T + stage + 1 ≤ maxRank := by omega
    have hcurrentWord : ((T + stage + 1 : ℕ) : ℤ) ≤ lim.word := by omega
    have hdiff : ((maxRank - T : ℕ) : ℤ) = (maxRank : ℤ) - (T : ℤ) := Nat.cast_sub hT
    unfold loopBody
    have hc := hcall hstage ν H
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
              LightTernaryEulerScan.time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hdiff, LightTernaryEulerScan.time] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hdiff, LightTernaryEulerScan.time] <;> omega)
      on_goal -1 => (rintro result ξ ⟨hresult, hs⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    refine ⟨by simp, result, ξ, ?_, H.next hvals hs⟩
    simp [update_frame_setLocal]
  case done => intro σ hcounter hshape; exact hshape
  case bound =>
    rintro stage _ hstage _ ⟨rval, ν, rfl, H⟩
    have hdiff : ((maxRank - T : ℕ) : ℤ) = (maxRank : ℤ) - (T : ℤ) := Nat.cast_sub hT
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
    refine ⟨rfl, H.1, ?_⟩
    intro j hj
    exact H.2 j hj (by have hmax := (hrankRange j hj).2; omega)
end ThreeSum.LightTernaryEulerMemo
