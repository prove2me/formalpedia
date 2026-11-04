-- Prove2me | solution 1 for ThreeSum.LightPrimeMinimum.Procs.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:12:46.326206+00:00
-- url     : https://prove2.me/submissions/ad51fd75-b425-441b-8371-fcf52c944945

import Definitions.Def_Submission_ThreeSum_LightWeightedScore
import Definitions.Def_Submission_ThreeSum_LightMinimum
import Definitions.Def_Submission_ThreeSum_LightPrimeMinimum
import Theorems.Thm_ThreeSum_LightPrimeMinimum_score_congr
import Theorems.Thm_Light_Ends_iteLast
import Theorems.Thm_Light_Ends_mono
import Theorems.Thm_Light_Ends_pieceThen
import Theorems.Thm_Light_Ends_skip
import Theorems.Thm_Light_MatAt_congr
import Theorems.Thm_Light_Meets_mono
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_SameOn_mono
import Theorems.Thm_Light_SameOutside_mono
import Theorems.Thm_Light_Seg_congr
import Theorems.Thm_Light_frame_append_zeros
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_Arithmetic_missWeight_zero
import Theorems.Thm_ThreeSum_CyclicFold_asPolynomial_replicate_zero
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_coeff
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_minus
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_negate
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_plus
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_shift
import Theorems.Thm_ThreeSum_Karatsuba_length_minus
import Theorems.Thm_ThreeSum_Karatsuba_length_negate
import Theorems.Thm_ThreeSum_Karatsuba_length_plus
import Theorems.Thm_ThreeSum_Karatsuba_length_shift
import Theorems.Thm_ThreeSum_Karatsuba_minus_getD
import Theorems.Thm_ThreeSum_Karatsuba_plus_getD
import Definitions.Def_WeightedCache3SUM_Alias_cd0e44d57dc54f82
import Theorems.Thm_ThreeSum_LightHistogram_count_zero
import Theorems.Thm_ThreeSum_LightKaratsuba_ProductAt_congr
import Definitions.Def_WeightedCache3SUM_Alias_54cf43efc96d8adf
import Theorems.Thm_ThreeSum_LightKaratsuba_window_sub
import Definitions.Def_WeightedCache3SUM_Alias_3252ff1ef14149f2
import Theorems.Thm_ThreeSum_LightMinimum_least_lt
import Theorems.Thm_ThreeSum_LightMinimum_least_lt_of_le
import Definitions.Def_WeightedCache3SUM_Alias_e1d95931a2ead3e4
import Theorems.Thm_ThreeSum_LightModuloCounts_Procs_meets
import Definitions.Def_WeightedCache3SUM_Alias_03cdb09d18890d4e
import Definitions.Def_WeightedCache3SUM_Alias_9b3006da0fcbdf4e
import Definitions.Def_WeightedCache3SUM_Alias_280261ae8ac7fab5
import Theorems.Thm_ThreeSum_WeightedScore_corrections_zero
import Theorems.Thm_ThreeSum_WeightedScore_remaining_le
import Theorems.Thm_ThreeSum_WeightedScore_remaining_zero
import Definitions.Def_WeightedCache3SUM_Alias_31b4729195398428
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.Arithmetic.missWeight_zero
attribute [local simp] ThreeSum.CyclicFold.asPolynomial_replicate_zero
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_coeff
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_minus
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_negate
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_plus
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_shift
attribute [local simp] ThreeSum.Karatsuba.length_minus
attribute [local simp] ThreeSum.Karatsuba.length_negate
attribute [local simp] ThreeSum.Karatsuba.length_plus
attribute [local simp] ThreeSum.Karatsuba.length_shift
attribute [local simp] ThreeSum.Karatsuba.minus_getD
attribute [local simp] ThreeSum.Karatsuba.plus_getD
attribute [local simp] ThreeSum.LightHistogram.count_zero
attribute [local simp] ThreeSum.LightKaratsuba.window_sub
attribute [local simp] ThreeSum.WeightedScore.corrections_zero
attribute [local simp] ThreeSum.WeightedScore.remaining_zero
set_option autoImplicit false
open ThreeSum ThreeSum.LightPrimeMinimum
open Light WeightedScore
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightPrimeMinimum
namespace Procs
theorem _root_.solution {pMain : ℕ} (S : Procs P pMain) {μ : ℕ → ℤ} {a b c nA nB nC q N aux s free maxMod U : ℕ}
    (primes : ℕ → ℕ) (hw : (lim.space : ℤ) ≤ lim.word) (hq : 0 < q) (hs : 0 < s) (ha : a + nA ≤ free)
    (hb : b + nB ≤ free) (hc : c + nC ≤ free) (haux : aux + s ≤ free) (hnA : nA ≤ N) (hnB : nB ≤ N) (hnC : nC ≤ N)
    (hspace : LightWeightedScore.space free maxMod N U ≤ lim.space)
    (hword : (LightWeightedScore.word maxMod N s U : ℤ) ≤ lim.word) (hd : d + Nat.clog 2 maxMod + 5 ≤ lim.depth)
    (hA : ∀ i < nA, |μ (a + i)| ≤ (U : ℤ)) (hB : ∀ i < nB, |μ (b + i)| ≤ (U : ℤ)) (hC : ∀ i < nC, |μ (c + i)| ≤ (U : ℤ))
    (hread : ∀ i < s, μ (aux + i) = (primes i : ℤ)) (hprime : ∀ i < s, Nat.Prime (primes i))
    (hinj : ∀ i < s, ∀ j < s, primes i = primes j → i = j)
    (hproduct : ∀ i < s, ∀ j < s, q * primes i * primes j ≤ maxMod) :
    Meets lim P pMain d [a, b, c, nA, nB, nC, q, N, aux, s, free] μ (time maxMod nA nB nC s U)
      (fun r μ' =>
        r = (chosenPrime primes s q nA nB nC (fun j => μ (a + j)) (fun j => μ (b + j)) (fun j => μ (c + j)) : ℤ) ∧
          Kept μ μ' free) :=
  by
  let A := fun j => μ (a + j)
  let B := fun j => μ (b + j)
  let C := fun j => μ (c + j)
  let f := candidateScore primes s q nA nB nC A B C
  let ct := LightWeightedScore.runtimeTime maxMod nA nB nC s U
  have hfree : free ≤ lim.space := by
    have hh := (Nat.le_max_right _ _).trans hspace
    change free + (Nat.log 2 (maxMod + 1) + 2) ≤ lim.space at hh
    omega
  have hprodN : nA * nB * nC ≤ N ^ 3 := by
    calc
      _ ≤ N * N * N := Nat.mul_le_mul (Nat.mul_le_mul hnA hnB) hnC
      _ = _ := by ring
  have hscoreWord : ((s * N ^ 3 : ℕ) : ℤ) ≤ lim.word :=
    by
    have hm : s * N ^ 3 ≤ (s + 1) * N ^ 3 := Nat.mul_le_mul_right _ (by omega)
    have hh : s * N ^ 3 ≤ LightWeightedScore.word maxMod N s U :=
      by
      unfold LightWeightedScore.word
      omega
    exact (Int.ofNat_le.mpr hh).trans hword
  have hf (i : ℕ) : 0 ≤ f i ∧ f i ≤ lim.word := by
    unfold f candidateScore
    constructor
    · positivity
    · rw [score_eq_remaining primes s (q * primes i) nA nB nC A B C hprime hinj]
      exact
        (Int.ofNat_le.mpr
              ((remaining_le primes s (q * primes i) nA nB nC A B C s).trans (Nat.mul_le_mul_left s hprodN))).trans
          hscoreWord
  have hmaxWord : (maxMod : ℤ) ≤ lim.word :=
    by
    have hh : maxMod ≤ LightWeightedScore.word maxMod N s U :=
      by
      unfold LightWeightedScore.word
      omega
    exact (Int.ofNat_le.mpr hh).trans hword
  have hqimax (i : ℕ) (hi : i < s) : q * primes i ≤ maxMod :=
    (Nat.le_mul_of_pos_right _ (hprime 0 hs).pos).trans (hproduct i hi 0 hs)
  have hpiWord (i : ℕ) (hi : i < s) : (primes i : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr ((Nat.le_mul_of_pos_left (primes i) hq).trans (hqimax i hi))).trans hmaxWord
  have hqiWord (i : ℕ) (hi : i < s) : (q : ℤ) * (primes i : ℤ) ≤ lim.word :=
    by
    have hh := (Int.ofNat_le.mpr (hqimax i hi)).trans hmaxWord
    exact_mod_cast hh
  have hcall (ν : ℕ → ℤ) (i : ℕ) (hi : i < s) (hkept : Kept μ ν free) :
    Meets lim P S.pScore (d + 1) [a, b, c, nA, nB, nC, q * primes i, N, aux, s, free] ν ct
      (fun r ν' => r = f i ∧ Kept ν ν' free) :=
    by
    have hAν : ∀ j < nA, |ν (a + j)| ≤ (U : ℤ) := by
      intro j hj
      rw [hkept _ (by omega)]
      exact hA j hj
    have hBν : ∀ j < nB, |ν (b + j)| ≤ (U : ℤ) := by
      intro j hj
      rw [hkept _ (by omega)]
      exact hB j hj
    have hCν : ∀ j < nC, |ν (c + j)| ≤ (U : ℤ) := by
      intro j hj
      rw [hkept _ (by omega)]
      exact hC j hj
    have hreadν : ∀ j < s, ν (aux + j) = (primes j : ℤ) :=
      by
      intro j hj
      exact (hkept _ (by omega)).trans (hread j hj)
    apply
      (S.score.meets (d := d + 1) primes hw (Nat.mul_pos hq (hprime i hi).pos) (hqimax i hi) ha hb hc haux hnA hnB hnC
            hspace hword (by omega) hAν hBν hCν hreadν hprime hinj (hproduct i hi)).mono
        le_rfl
    intro r ν' ⟨hr, hkeep⟩
    refine ⟨hr.trans ?_, hkeep⟩
    unfold f candidateScore
    congr 1
    exact score_congr (fun j hj => hkept _ (by omega)) (fun j hj => hkept _ (by omega)) (fun j hj => hkept _ (by omega))
  have hp0 := hpiWord 0 hs
  have hq0 := hqiWord 0 hs
  have hq0nonneg : (0 : ℤ) ≤ (q : ℤ) * (primes 0 : ℤ) := by positivity
  have hread0 : μ aux = (primes 0 : ℤ) := by simpa using hread 0 hs
  apply Meets.of_body S.main
  unfold body time
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
    | refine _root_.Light.Ends.callToThen ((hcall μ 0 hs (fun _ _ => rfl)) _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen (hcall μ 0 hs (fun _ _ => rfl)) ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hread0, ct]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hread0, ct] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hread0, ct] <;> omega)
    on_goal -1 => (rintro result μ₀ ⟨hresult, hkept₀⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  subst result
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
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
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
  refine
    Ends.pieceThen
      (Ends.for (T := s * (ct + 100) + 20) (Q := Inv μ f a b c nA nB nC q N aux s free s)
        (Inv μ f a b c nA nB nC q N aux s free) s (ct + 80) ?_ ?_ ?_ ?_ (hT := by
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ct]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [ct] <;> first
              | omega
              | (ring_nf; omega))))
      ?_ (hT := by
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ct]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [ct] <;> first
            | omega
            | (ring_nf; omega)))
  · refine ⟨0, μ₀, ?_, hkept₀⟩
    simp only [LightMinimum.least, update_frame_setLocal]
    exact congrArg (fun loc => (⟨loc, μ₀⟩ : State)) (frame_append_zeros _ 1).symm
  · rintro i _ hi _ ⟨rval, ν, rfl, hkept⟩
    have hbest : LightMinimum.least f i < s := LightMinimum.least_lt_of_le f hs (by omega)
    have hpi := hpiWord i hi
    have hqi := hqiWord i hi
    have hqinonneg : (0 : ℤ) ≤ (q : ℤ) * (primes i : ℤ) := by positivity
    have hreadν : ν (aux + i) = (primes i : ℤ) := (hkept _ (by omega)).trans (hread i hi)
    have hfi := hf i
    have hfb := hf (LightMinimum.least f i)
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
      | refine _root_.Light.Ends.callToThen ((hcall ν i hi hkept) _ (by omega)) ?_ ?_ ?_ ?_
      | refine _root_.Light.Ends.callToThen (hcall ν i hi hkept) ?_ ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hreadν, ct]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hreadν, ct] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hreadν, ct] <;> omega)
      on_goal -1 => (rintro result ν₁ ⟨hresult, hkeep₁⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    subst result
    have hkept₁ : Kept μ ν₁ free := fun j hj => (hkeep₁ j hj).trans (hkept j hj)
    refine
      Ends.iteLast (fun hcmp => ?_) (fun hcmp => ?_)
        (by (
            (try have := _root_.Light.Std.space_le (by assumption))
            (try have := _root_.Light.Std.const_le (by assumption))
            simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
    · have hcmp' : f i < f (LightMinimum.least f i) := by simpa using hcmp
      focus
        ((first
            | refine _root_.Light.Ends.seqSelf ?_
            | refine _root_.Light.Ends.skipLast ?_);
          (repeat
              with_unfolding_none
                first
                | refine _root_.Light.Ends.seqAssoc ?_
                | refine _root_.Light.Ends.skipThen ?_))
        refine _root_.Light.Ends.setToThen (f i) ?_ ?_ ?_
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
      focus
        ((first
            | refine _root_.Light.Ends.seqSelf ?_
            | refine _root_.Light.Ends.skipLast ?_);
          (repeat
              with_unfolding_none
                first
                | refine _root_.Light.Ends.seqAssoc ?_
                | refine _root_.Light.Ends.skipThen ?_))
        refine _root_.Light.Ends.setToThen i ?_ ?_ ?_
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
      refine ⟨by simp, f i, ν₁, ?_, hkept₁⟩
      simp [LightMinimum.least, hcmp', update_frame_setLocal]
    · have hcmp' : ¬f i < f (LightMinimum.least f i) := by simpa using hcmp
      apply Ends.skip
      refine ⟨by simp, f i, ν₁, ?_, hkept₁⟩
      simp [LightMinimum.least, hcmp', update_frame_setLocal]
  · intro σ _ hI
    exact hI
  · rintro i _ hi _ ⟨rval, ν, rfl, hkept⟩
    simp
  · rintro σ ⟨rval, ν, rfl, hkept⟩
    have hbest : LightMinimum.least f s < s := LightMinimum.least_lt f hs
    have hbestWord := hpiWord (LightMinimum.least f s) hbest
    have hreadBest : ν (aux + LightMinimum.least f s) = (primes (LightMinimum.least f s) : ℤ) :=
      (hkept _ (by omega)).trans (hread _ hbest)
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        (repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_))
      refine _root_.Light.Ends.setToThen (primes (LightMinimum.least f s)) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hreadBest, ct]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hreadBest, ct] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hreadBest, ct] <;> omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    exact ⟨by simp [chosenPrime, chosenIndex, f, A, B, C], hkept⟩
end Procs
end ThreeSum.LightPrimeMinimum
