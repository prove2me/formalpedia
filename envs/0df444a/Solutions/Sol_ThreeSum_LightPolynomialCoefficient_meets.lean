-- Prove2me | solution 1 for ThreeSum.LightPolynomialCoefficient.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:17:20.271458+00:00
-- url     : https://prove2.me/submissions/e44cace3-cbcc-4bb1-93c9-a7be8b85383f

import Definitions.Def_Submission_ThreeSum_LightRadixDigit
import Definitions.Def_Submission_ThreeSum_LightPolynomialCoefficient
import Theorems.Thm_ThreeSum_LightPolynomialCoefficient_raw_zero
import Theorems.Thm_ThreeSum_LightPolynomialCoefficient_raw_succ
import Theorems.Thm_ThreeSum_LightPolynomialCoefficient_raw_bound
import Theorems.Thm_Light_Ends_iteLast
import Theorems.Thm_Light_Ends_pieceThen
import Theorems.Thm_Light_Ends_setLast
import Theorems.Thm_Light_Ends_skip
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.LightPolynomialCoefficient.raw_zero
set_option autoImplicit false
open ThreeSum ThreeSum.LightPolynomialCoefficient
open Light Finset
set_option maxHeartbeats 2000000
variable {lim : Limits} {P : Program} {depth : ℕ}
namespace ThreeSum.LightPolynomialCoefficient
theorem _root_.solution {proc srcA srcB n m k p : ℕ} (hp : P[proc]? = some body) (μ : ℕ → ℤ) (f g : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hA : srcA + n ≤ lim.space) (hB : srcB + m ≤ lim.space)
    (hreadA : ∀ i < n, μ (srcA + i) = (f i : ℤ)) (hreadB : ∀ i < m, μ (srcB + i) = (g i : ℤ)) (hf : ∀ i < n, f i < p)
    (hg : ∀ i < m, g i < p) (hword : (((n + 1) * (p + 1) ^ 2 + k + m + 10 : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P proc depth [srcA, srcB, n, m, k] μ (time n) (fun r ν => r = (rawCoefficient f g n m k : ℤ) ∧ ν = μ) :=
  by
  have hb (z : ℕ) (hz : z ≤ (n + 1) * (p + 1) ^ 2 + k + m + 10) : (z : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr hz).trans hword
  have hkw := hb k (by omega)
  have hmw := hb m (by omega)
  have hnp : n * p ^ 2 ≤ (n + 1) * (p + 1) ^ 2 + k + m + 10 := by
    calc
      n * p ^ 2 ≤ (n + 1) * (p + 1) ^ 2 := Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left (by omega) 2)
      _ ≤ _ := by omega
  have hfit (j : ℕ) (hj : j ≤ n) : (rawCoefficient f g j m k : ℤ) ≤ lim.word :=
    hb _ ((raw_bound f g hf hg hj).trans ((Nat.mul_le_mul_right (p ^ 2) hj).trans hnp))
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
  refine
    Ends.pieceThen
      (Ends.for (T := 100 * n + 6) (Q := fun σ => σ = ⟨frame [srcA, srcB, n, m, k, rawCoefficient f g n m k, n], μ⟩)
        (fun j σ => σ = ⟨frame [srcA, srcB, n, m, k, rawCoefficient f g j m k, j], μ⟩) n 80 ?start ?round ?done ?bound
        (hT := by
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
      ?after
  case start => simp [raw_zero, update_frame_setLocal]
  case round =>
    rintro j _ hj _ rfl
    have hsum0 := hfit j (by omega)
    have hsum1 := hfit (j + 1) (by omega)
    unfold loopBody
    refine
      Ends.iteLast ?_ ?_
        (by (
            (try have := _root_.Light.Std.space_le (by assumption))
            (try have := _root_.Light.Std.const_le (by assumption))
            simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
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
    · intro hle
      have hjk : j ≤ k := by
        have hh : (j : ℤ) < (k : ℤ) + 1 := by simpa using hle
        omega
      have hsub : (k : ℤ) - (j : ℤ) = ((k - j : ℕ) : ℤ) := (Int.natCast_sub hjk).symm
      refine
        Ends.iteLast ?_ ?_
          (by (
              (try have := _root_.Light.Std.space_le (by assumption))
              (try have := _root_.Light.Std.const_le (by assumption))
              simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hsub] <;> omega))
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
      · intro hlt
        have hkm : k - j < m :=
          by
          have hh : ((k - j : ℕ) : ℤ) < (m : ℤ) := by
            simpa only [Cond.Holds, Expr.val, Op.eval, frame, List.getD_cons_zero, List.getD_cons_succ, hsub] using hlt
          exact_mod_cast hh
        have hrA := hreadA j hj
        have hrB := hreadB (k - j) hkm
        have hf' := hf j hj
        have hg' := hg (k - j) hkm
        have hprod : f j * g (k - j) ≤ n * p ^ 2 := by nlinarith
        have hprodWord := hb (f j * g (k - j)) (hprod.trans hnp)
        have hsucc : rawCoefficient f g (j + 1) m k = rawCoefficient f g j m k + f j * g (k - j) := by
          rw [raw_succ, term, if_pos ⟨hjk, hkm⟩]
        have hsuccZ :
          (rawCoefficient f g j m k : ℤ) + (f j : ℤ) * (g (k - j) : ℤ) = (rawCoefficient f g (j + 1) m k : ℤ) := by
          exact_mod_cast hsucc.symm
        refine
          Ends.setLast ?_ (hs := by
            ( (try have := _root_.Light.Std.space_le (by assumption))
              (try have := _root_.Light.Std.const_le (by assumption))
              simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hrA, hrB, hsub, ← hsucc] <;> omega))
            (hT := by
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
        simp [hrA, hrB, hsub, hsuccZ, update_frame_setLocal]
      · intro hlt
        have hkm : ¬k - j < m :=
          by
          have hh : ¬((k - j : ℕ) : ℤ) < (m : ℤ) := by
            simpa only [Cond.Holds, Expr.val, Op.eval, frame, List.getD_cons_zero, List.getD_cons_succ, hsub] using hlt
          exact_mod_cast hh
        have hsame : rawCoefficient f g (j + 1) m k = rawCoefficient f g j m k := by simp [raw_succ, term, hkm]
        exact Ends.skip (by simp [hsame, update_frame_setLocal])
    · intro hle
      have hjk : ¬j ≤ k := by
        have hh : (k : ℤ) + 1 ≤ (j : ℤ) := by simpa using hle
        omega
      have hsame : rawCoefficient f g (j + 1) m k = rawCoefficient f g j m k := by simp [raw_succ, term, hjk]
      exact Ends.skip (by simp [hsame, update_frame_setLocal])
  case done => intro σ hcounter hshape; exact hshape
  case bound =>
    rintro j _ hj _ rfl
    ( (try have := _root_.Light.Std.space_le (by assumption))
      (try have := _root_.Light.Std.const_le (by assumption))
      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
  case after =>
    intro σ hshape
    rw [hshape]
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.setToThen (rawCoefficient f g n m k : ℕ) ?_ ?_ ?_
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
end ThreeSum.LightPolynomialCoefficient
