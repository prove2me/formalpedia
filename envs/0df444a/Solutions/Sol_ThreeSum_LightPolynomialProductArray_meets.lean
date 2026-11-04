-- Prove2me | solution 1 for ThreeSum.LightPolynomialProductArray.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:25:34.191948+00:00
-- url     : https://prove2.me/submissions/7901e293-a327-4f9c-bb72-1022aa239b34

import Definitions.Def_Submission_ThreeSum_LightPolynomialCoefficient
import Definitions.Def_Submission_ThreeSum_LightCoefficientDecode
import Definitions.Def_Submission_ThreeSum_LightPolynomialProductArray
import Theorems.Thm_Light_LocalsBut_update
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_SameOn_refl
import Theorems.Thm_Light_SameOutside2_refl
import Theorems.Thm_Light_SameOutside_refl
import Theorems.Thm_Light_frame_append_zeros
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_LightPolynomialCoefficient_raw_bound
import Theorems.Thm_ThreeSum_LightPolynomialCoefficient_raw_zero
import Theorems.Thm_ThreeSum_LightPolynomialCoefficient_reduced_meets
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
attribute [local simp] ThreeSum.LightPolynomialCoefficient.raw_zero
set_option autoImplicit false
open ThreeSum ThreeSum.LightPolynomialProductArray
open Light
set_option maxHeartbeats 2000000
variable {lim : Limits} {P : Program} {depth : ℕ}
namespace ThreeSum.LightPolynomialProductArray
theorem _root_.solution {proc pCoefficient pRaw pDigit pDivide srcA srcB dst n m len p : ℕ}
    (hp : P[proc]? = some (body pCoefficient))
    (hcoeff : P[pCoefficient]? = some (LightPolynomialCoefficient.reducedBody pRaw pDigit))
    (hraw : P[pRaw]? = some LightPolynomialCoefficient.body) (hdigit : P[pDigit]? = some (LightRadixDigit.body pDivide))
    (hdivide : P[pDivide]? = some LightSmallDivide.body) (μ : ℕ → ℤ) (f g : ℕ → ℕ) (hw : (lim.space : ℤ) ≤ lim.word)
    (hd : depth + 2 < lim.depth) (hA : srcA + n ≤ dst) (hB : srcB + m ≤ dst) (hD : dst + len ≤ lim.space)
    (hreadA : ∀ i < n, μ (srcA + i) = (f i : ℤ)) (hreadB : ∀ i < m, μ (srcB + i) = (g i : ℤ)) (hf : ∀ i < n, f i < p)
    (hg : ∀ i < m, g i < p) (hword : ((20 * ((n + 1) * (p + 1) ^ 2 + len + m + 10) : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P proc depth [srcA, srcB, n, m, len, p, dst] μ (time n p len)
      (fun _ ν =>
        (∀ k < len, ν (dst + k) = (LightPolynomialCoefficient.coefficient p f g n m k : ℤ)) ∧
          SameOutside μ ν dst len) :=
  by
  apply Meets.of_body hp
  unfold body time
  refine
    Ends.for (Inv μ srcA srcB n m len p dst f g) len (LightPolynomialCoefficient.reducedTime n p + 90) ?start ?round
      ?done ?bound
  case start =>
    refine ⟨0, μ, ?_, ?_, SameOutside.refl⟩
    · exact congrArg (fun loc => (⟨loc, μ⟩ : State)) ((update_frame_setLocal _ _ _).trans (frame_append_zeros _ 1).symm)
    · intro k hk; omega
  case round =>
    rintro j _ hj _ ⟨old, ν, rfl, written, kept⟩
    have hwordJ : ((20 * ((n + 1) * (p + 1) ^ 2 + j + m + 10) : ℕ) : ℤ) ≤ lim.word := by omega
    have hrA (i : ℕ) (hi : i < n) : ν (srcA + i) = (f i : ℤ) := (kept _ (Or.inl (by omega))).trans (hreadA i hi)
    have hrB (i : ℕ) (hi : i < m) : ν (srcB + i) = (g i : ℤ) := (kept _ (Or.inl (by omega))).trans (hreadB i hi)
    have hbudget : (LightPolynomialCoefficient.coefficient p f g n m j : ℤ) ≤ lim.word :=
      by
      have hh := Nat.mod_le (LightPolynomialCoefficient.rawCoefficient f g n m j) p
      have hb := LightPolynomialCoefficient.raw_bound f g hf hg (j := n) le_rfl (k := j)
      have hfit : n * p ^ 2 ≤ 20 * ((n + 1) * (p + 1) ^ 2 + len + m + 10) :=
        by
        have hh : n * p ^ 2 ≤ (n + 1) * (p + 1) ^ 2 := Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left (by omega) 2)
        omega
      exact (Int.ofNat_le.mpr (hh.trans (hb.trans hfit))).trans hword
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
            ((LightPolynomialCoefficient.reduced_meets (depth := depth + 1) hcoeff hraw hdigit hdivide ν f g hw
                (by omega) (by omega) (by omega) hrA hrB hf hg hwordJ)
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          _root_.Light.Ends.callToThen
            (LightPolynomialCoefficient.reduced_meets (depth := depth + 1) hcoeff hraw hdigit hdivide ν f g hw
              (by omega) (by omega) (by omega) hrA hrB hf hg hwordJ)
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
      on_goal -1 => (rintro result ν₁ ⟨hresult, hν₁⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    subst ν₁
    subst result
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.storeToThen (dst + j) (LightPolynomialCoefficient.coefficient p f g n m j : ℕ) ?_ ?_ ?_
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
      ⟨by simp, (LightPolynomialCoefficient.coefficient p f g n m j : ℤ),
        Function.update ν (dst + j) (LightPolynomialCoefficient.coefficient p f g n m j : ℤ), by
        simp [update_frame_setLocal], ?_, kept.update ⟨by omega, by omega⟩ _⟩
    intro k hk
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · rw [Function.update_of_ne (by omega)]
      exact written k hk
    · simp
  case done => rintro _ _ ⟨r, ν, rfl, written, kept⟩; exact ⟨written, kept⟩
  case bound =>
    rintro j _ _ _ ⟨r, ν, rfl, _, _⟩
    ( (try have := _root_.Light.Std.space_le (by assumption))
      (try have := _root_.Light.Std.const_le (by assumption))
      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
end ThreeSum.LightPolynomialProductArray
