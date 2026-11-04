-- Prove2me | solution 1 for ThreeSum.LightPrimeAddArray.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:27:58.214073+00:00
-- url     : https://prove2.me/submissions/7c95982f-c0a1-48ac-b2b1-8a920f99aba5

import Definitions.Def_Submission_ThreeSum_LightPrimeCoefficient
import Definitions.Def_Submission_ThreeSum_LightCoefficientDecode
import Definitions.Def_Submission_ThreeSum_LightPrimeAddArray
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
import Theorems.Thm_ThreeSum_LightPrimeCoefficient_mulAdd_meets
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
set_option autoImplicit false
open ThreeSum ThreeSum.LightPrimeAddArray
open Light
set_option maxHeartbeats 2000000
variable {lim : Limits} {P : Program} {depth : ℕ}
namespace ThreeSum.LightPrimeAddArray
theorem _root_.solution {proc pMulAdd pDivide srcA srcB dst n p : ℕ} (hp : P[proc]? = some (body pMulAdd))
    (hadd : P[pMulAdd]? = some (LightPrimeCoefficient.mulAddBody pDivide))
    (hdivide : P[pDivide]? = some LightSmallDivide.body) (μ : ℕ → ℤ) (f g : ℕ → ℕ) (hw : (lim.space : ℤ) ≤ lim.word)
    (hd : depth + 1 < lim.depth) (hpp : 1 < p) (hA : srcA + n ≤ dst) (hB : srcB + n ≤ dst) (hD : dst + n ≤ lim.space)
    (hreadA : ∀ i < n, μ (srcA + i) = (f i : ℤ)) (hreadB : ∀ i < n, μ (srcB + i) = (g i : ℤ)) (hf : ∀ i < n, f i < p)
    (hg : ∀ i < n, g i < p) (hword : (LightPrimeCoefficient.word p : ℤ) ≤ lim.word) :
    Meets lim P proc depth [srcA, srcB, dst, n, p] μ (time n p)
      (fun _ ν => (∀ i < n, ν (dst + i) = (((f i + g i) % p : ℕ) : ℤ)) ∧ SameOutside μ ν dst n) :=
  by
  have hpWord : (p : ℤ) ≤ lim.word :=
    by
    have hh : p ≤ LightPrimeCoefficient.word p := by unfold LightPrimeCoefficient.word; nlinarith
    exact (Int.ofNat_le.mpr hh).trans hword
  have h1 : (1 : ℤ) ≤ lim.word := by omega
  apply Meets.of_body hp
  unfold body time
  refine Ends.for (Inv μ srcA srcB dst n p f g) n (LightPrimeCoefficient.mulAddTime p + 50) ?start ?round ?done ?bound
  case start =>
    refine ⟨0, μ, ?_, ?_, SameOutside.refl⟩
    · exact congrArg (fun loc => (⟨loc, μ⟩ : State)) ((update_frame_setLocal _ _ _).trans (frame_append_zeros _ 1).symm)
    · intro j hj; omega
  case round =>
    rintro j _ hj _ ⟨old, ν, rfl, written, kept⟩
    have hrA : ν (srcA + j) = (f j : ℤ) := (kept _ (Or.inl (by omega))).trans (hreadA j hj)
    have hrB : ν (srcB + j) = (g j : ℤ) := (kept _ (Or.inl (by omega))).trans (hreadB j hj)
    have hf' := hf j hj
    have hg' := hg j hj
    have hfw : (f j : ℤ) ≤ lim.word := (by exact_mod_cast (Nat.le_of_lt hf') : (f j : ℤ) ≤ (p : ℤ)).trans hpWord
    have hgw : (g j : ℤ) ≤ lim.word := (by exact_mod_cast (Nat.le_of_lt hg') : (g j : ℤ) ≤ (p : ℤ)).trans hpWord
    have hresWord : (((f j + g j) % p : ℕ) : ℤ) ≤ lim.word :=
      (by exact_mod_cast Nat.le_of_lt (Nat.mod_lt _ (by omega : 0 < p)) : (((f j + g j) % p : ℕ) : ℤ) ≤ (p : ℤ)).trans
        hpWord
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
            ((LightPrimeCoefficient.mulAdd_meets (d := depth + 1) (acc := f j) (x := 1) (y := g j) (p := p) hadd hdivide
                ν (by omega) (by omega) hf' hpp hg' hword)
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          _root_.Light.Ends.callToThen
            (LightPrimeCoefficient.mulAdd_meets (d := depth + 1) (acc := f j) (x := 1) (y := g j) (p := p) hadd hdivide
              ν (by omega) (by omega) hf' hpp hg' hword)
            ?_ ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hrA, hrB,
              LightPrimeCoefficient.mulAddTime]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hrA, hrB, LightPrimeCoefficient.mulAddTime] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hrA, hrB,
              LightPrimeCoefficient.mulAddTime] <;>
            omega)
      on_goal -1 => (rintro result ν₁ ⟨hresult, hν₁⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    subst ν₁
    have hr : result = (((f j + g j) % p : ℕ) : ℤ) := by simpa using hresult
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.storeToThen (dst + j) ((f j + g j) % p : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hr,
              LightPrimeCoefficient.mulAddTime]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hr, LightPrimeCoefficient.mulAddTime] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hr, LightPrimeCoefficient.mulAddTime] <;>
            omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    refine
      ⟨by simp, result, Function.update ν (dst + j) (((f j + g j) % p : ℕ) : ℤ), by simp [update_frame_setLocal], ?_,
        kept.update ⟨by omega, by omega⟩ _⟩
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [Function.update_of_ne (by omega)]
      exact written i hi
    · simp
  case done => rintro _ _ ⟨r, ν, rfl, written, kept⟩; exact ⟨written, kept⟩
  case bound =>
    rintro j _ _ _ ⟨r, ν, rfl, _, _⟩
    ( (try have := _root_.Light.Std.space_le (by assumption))
      (try have := _root_.Light.Std.const_le (by assumption))
      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
end ThreeSum.LightPrimeAddArray
