-- Prove2me | solution 1 for ThreeSum.LightPolynomialProductCheck.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:25:33.006213+00:00
-- url     : https://prove2.me/submissions/664263e3-0d72-43fc-b773-bcc8aad7f593

import Definitions.Def_Submission_ThreeSum_LightPolynomialCoefficient
import Definitions.Def_Submission_ThreeSum_LightPolynomialProductCheck
import Theorems.Thm_ThreeSum_LightPolynomialProductCheck_valid_succ
import Theorems.Thm_ThreeSum_LightPolynomialProductCheck_flag_zero
import Theorems.Thm_ThreeSum_LightPolynomialProductCheck_flag_bounds
import Theorems.Thm_Light_Ends_iteLast
import Theorems.Thm_Light_Ends_pieceThen
import Theorems.Thm_Light_Ends_skip
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_frame_append_zeros
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_LightPolynomialCoefficient_raw_bound
import Theorems.Thm_ThreeSum_LightPolynomialCoefficient_raw_zero
import Theorems.Thm_ThreeSum_LightPolynomialCoefficient_reduced_meets
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.LightPolynomialCoefficient.raw_zero
set_option autoImplicit false
open ThreeSum ThreeSum.LightPolynomialProductCheck
open Light
set_option maxHeartbeats 2000000
attribute [local instance] ThreeSum.LightPolynomialProductCheck._p2m_local_instance_3bb6a27167_6
variable {lim : Limits} {P : Program} {depth : ℕ}
namespace ThreeSum.LightPolynomialProductCheck
theorem _root_.solution {proc pCoefficient pRaw pDigit pDivide srcA srcB dst n m len p : ℕ}
    (hp : P[proc]? = some (body pCoefficient))
    (hcoeff : P[pCoefficient]? = some (LightPolynomialCoefficient.reducedBody pRaw pDigit))
    (hraw : P[pRaw]? = some LightPolynomialCoefficient.body) (hdigit : P[pDigit]? = some (LightRadixDigit.body pDivide))
    (hdivide : P[pDivide]? = some LightSmallDivide.body) (μ : ℕ → ℤ) (f g expected : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : depth + 2 < lim.depth) (hA : srcA + n ≤ lim.space)
    (hB : srcB + m ≤ lim.space) (hD : dst + len ≤ lim.space) (hreadA : ∀ i < n, μ (srcA + i) = (f i : ℤ))
    (hreadB : ∀ i < m, μ (srcB + i) = (g i : ℤ)) (hreadD : ∀ i < len, μ (dst + i) = (expected i : ℤ))
    (hf : ∀ i < n, f i < p) (hg : ∀ i < m, g i < p)
    (hword : ((20 * ((n + 1) * (p + 1) ^ 2 + len + m + 10) : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P proc depth [srcA, srcB, dst, n, m, len, p] μ (time n p len)
      (fun r ν => r = flag p f g expected n m len ∧ ν = μ) :=
  by
  have hpp : (p : ℤ) ≤ lim.word :=
    by
    have hh : p ≤ 20 * ((n + 1) * (p + 1) ^ 2 + len + m + 10) := by nlinarith
    exact (Int.ofNat_le.mpr hh).trans hword
  have hone : (1 : ℤ) ≤ lim.word := by omega
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
    refine _root_.Light.Ends.setToThen (1 : ℕ) ?_ ?_ ?_
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
      (Ends.for (T := len * (LightPolynomialCoefficient.reducedTime n p + 100) + 6) (Q :=
        Inv μ srcA srcB dst n m len p f g expected len) (Inv μ srcA srcB dst n m len p f g expected) len
        (LightPolynomialCoefficient.reducedTime n p + 90) ?start ?round ?done ?bound)
      ?finish
  case start =>
    refine ⟨0, ?_⟩
    simp only [flag_zero]
    exact congrArg (fun loc => (⟨loc, μ⟩ : State)) ((update_frame_setLocal _ _ _).trans (frame_append_zeros _ 1).symm)
  case round =>
    rintro j _ hj _ ⟨old, rfl⟩
    have hwordJ : ((20 * ((n + 1) * (p + 1) ^ 2 + j + m + 10) : ℕ) : ℤ) ≤ lim.word := by omega
    have hbudget : (coefficient p f g n m j : ℤ) ≤ lim.word :=
      by
      have hh : coefficient p f g n m j ≤ LightPolynomialCoefficient.rawCoefficient f g n m j := Nat.mod_le _ _
      have hb := LightPolynomialCoefficient.raw_bound f g hf hg (j := n) le_rfl (k := j)
      have hfit : n * p ^ 2 ≤ 20 * ((n + 1) * (p + 1) ^ 2 + len + m + 10) :=
        by
        have hh : n * p ^ 2 ≤ (n + 1) * (p + 1) ^ 2 := Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left (by omega) 2)
        omega
      exact (Int.ofNat_le.mpr (hh.trans (hb.trans hfit))).trans hword
    have hflags := flag_bounds p f g expected n m j
    have hflags' := flag_bounds p f g expected n m (j + 1)
    have hread := hreadD j hj
    unfold roundBody
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
            ((LightPolynomialCoefficient.reduced_meets (depth := depth + 1) hcoeff hraw hdigit hdivide μ f g hw
                (by omega) hA hB hreadA hreadB hf hg hwordJ)
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          _root_.Light.Ends.callToThen
            (LightPolynomialCoefficient.reduced_meets (depth := depth + 1) hcoeff hraw hdigit hdivide μ f g hw
              (by omega) hA hB hreadA hreadB hf hg hwordJ)
            ?_ ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil,
              LightPolynomialCoefficient.reducedTime]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [LightPolynomialCoefficient.reducedTime] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightPolynomialCoefficient.reducedTime] <;>
            omega)
      on_goal -1 => (rintro result ν ⟨hresult, hν⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    subst ν
    subst result
    refine
      Ends.iteLast ?_ ?_
        (by (
            (try have := _root_.Light.Std.space_le (by assumption))
            (try have := _root_.Light.Std.const_le (by assumption))
            simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hread] <;> omega))
        (by
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
                | (ring_nf; omega)))
    · intro heq
      have he : expected j = coefficient p f g n m j :=
        by
        have hh : (coefficient p f g n m j : ℤ) = (expected j : ℤ) := by simpa [hread] using heq
        exact_mod_cast hh.symm
      have hflag : flag p f g expected n m (j + 1) = flag p f g expected n m j := by simp [flag, valid_succ, he]
      exact Ends.skip ⟨by simp, (coefficient p f g n m j : ℤ), by simp [hflag, update_frame_setLocal]⟩
    · intro hneq
      have he : expected j ≠ coefficient p f g n m j := by
        intro he
        apply hneq
        simp [hread, he]
      have hflag : flag p f g expected n m (j + 1) = 0 := by simp [flag, valid_succ, he]
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
      exact ⟨by simp, (coefficient p f g n m j : ℤ), by simp [hflag, update_frame_setLocal]⟩
  case done => rintro _ _ h; exact h
  case bound =>
    rintro j _ _ _ ⟨r, rfl⟩
    ( (try have := _root_.Light.Std.space_le (by assumption))
      (try have := _root_.Light.Std.const_le (by assumption))
      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
  case finish =>
    rintro _ ⟨r, rfl⟩
    have hf := flag_bounds p f g expected n m len
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.setToThen (flag p f g expected n m len) ?_ ?_ ?_
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
end ThreeSum.LightPolynomialProductCheck
