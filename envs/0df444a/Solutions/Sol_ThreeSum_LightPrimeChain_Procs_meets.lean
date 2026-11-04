-- Prove2me | solution 1 for ThreeSum.LightPrimeChain.Procs.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:20:39.759644+00:00
-- url     : https://prove2.me/submissions/f2734320-dd9f-44a6-8e98-fc3c6c6ca36f

import Definitions.Def_Submission_ThreeSum_LightPrimeMinimum
import Definitions.Def_Submission_ThreeSum_PrimeChain
import Definitions.Def_Submission_ThreeSum_LightPrimeChain
import Theorems.Thm_ThreeSum_LightPrimeChain_modulus_pos
import Theorems.Thm_ThreeSum_LightPrimeChain_modulus_bounds
import Theorems.Thm_Light_Ends_pieceThen
import Theorems.Thm_Light_LocalsBut_update
import Theorems.Thm_Light_Meets_of_body
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
import Definitions.Def_WeightedCache3SUM_Alias_54cf43efc96d8adf
import Theorems.Thm_ThreeSum_LightKaratsuba_window_sub
import Definitions.Def_WeightedCache3SUM_Alias_3252ff1ef14149f2
import Definitions.Def_WeightedCache3SUM_Alias_e1d95931a2ead3e4
import Theorems.Thm_ThreeSum_LightModuloCounts_Procs_meets
import Definitions.Def_WeightedCache3SUM_Alias_03cdb09d18890d4e
import Theorems.Thm_ThreeSum_LightPrimeMinimum_Procs_meets
import Theorems.Thm_ThreeSum_LightPrimeMinimum_chosenPrime_congr
import Definitions.Def_WeightedCache3SUM_Alias_9b3006da0fcbdf4e
import Definitions.Def_WeightedCache3SUM_Alias_280261ae8ac7fab5
import Theorems.Thm_ThreeSum_PrimeChain_modulus_bounds
import Theorems.Thm_ThreeSum_WeightedScore_corrections_zero
import Theorems.Thm_ThreeSum_WeightedScore_remaining_zero
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
open ThreeSum ThreeSum.LightPrimeChain
open Light WeightedScore LightPrimeMinimum Finset
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightPrimeChain
namespace Procs
theorem _root_.solution {pMain : ℕ} (S : Procs P pMain) {μ : ℕ → ℤ} {a b c nA nB nC N aux s levels free maxMod U Y : ℕ}
    (primes : ℕ → ℕ) (hw : (lim.space : ℤ) ≤ lim.word) (hs : 0 < s) (ha : a + nA ≤ free) (hb : b + nB ≤ free)
    (hc : c + nC ≤ free) (haux : aux + s ≤ free) (hnA : nA ≤ N) (hnB : nB ≤ N) (hnC : nC ≤ N)
    (hspace : space free maxMod N U levels ≤ lim.space) (hword : (LightWeightedScore.word maxMod N s U : ℤ) ≤ lim.word)
    (hd : d + Nat.clog 2 maxMod + 6 ≤ lim.depth) (hA : ∀ i < nA, |μ (a + i)| ≤ (U : ℤ))
    (hB : ∀ i < nB, |μ (b + i)| ≤ (U : ℤ)) (hC : ∀ i < nC, |μ (c + i)| ≤ (U : ℤ))
    (hread : ∀ i < s, μ (aux + i) = (primes i : ℤ)) (hprime : ∀ i < s, Nat.Prime (primes i))
    (hinj : ∀ i < s, ∀ j < s, primes i = primes j → i = j) (hhi : ∀ i < s, primes i ≤ Y)
    (hmax : Y ^ (levels + 1) ≤ maxMod) :
    Meets lim P pMain d [a, b, c, nA, nB, nC, N, aux, s, levels, free] μ (time maxMod nA nB nC s U levels)
      (fun r μ' =>
        r = (modulus primes s nA nB nC (fun j => μ (a + j)) (fun j => μ (b + j)) (fun j => μ (c + j)) levels : ℤ) ∧
          (∀ i ≤ levels,
              μ' (free + i) =
                (modulus primes s nA nB nC (fun j => μ (a + j)) (fun j => μ (b + j)) (fun j => μ (c + j)) i : ℤ)) ∧
            Kept μ μ' free) :=
  by
  let A := fun j => μ (a + j)
  let B := fun j => μ (b + j)
  let C := fun j => μ (c + j)
  let qs := modulus primes s nA nB nC A B C
  let ct := LightPrimeMinimum.time maxMod nA nB nC s U
  have hwork : free + levels + 1 ≤ lim.space :=
    by
    have hh := (Nat.le_max_right _ _).trans hspace
    change free + levels + 1 + (Nat.log 2 (maxMod + 1) + 2) ≤ lim.space at hh
    omega
  have hY : 1 ≤ Y := (hprime 0 hs).one_lt.le.trans (hhi 0 hs)
  have hqpos (i : ℕ) : 0 < qs i := modulus_pos primes A B C hs hprime i
  have hqhi (i : ℕ) : qs i ≤ Y ^ i := (modulus_bounds primes A B C hs 0 Y i (fun _ _ => Nat.zero_le _) hhi).2
  have hmaxWord : (maxMod : ℤ) ≤ lim.word :=
    by
    have hh : maxMod ≤ LightWeightedScore.word maxMod N s U :=
      by
      unfold LightWeightedScore.word
      omega
    exact (Int.ofNat_le.mpr hh).trans hword
  have hqWord (i : ℕ) (hi : i ≤ levels) : (qs i : ℤ) ≤ lim.word :=
    by
    have hh : qs i ≤ maxMod := (hqhi i).trans ((Nat.pow_le_pow_right hY (by omega : i ≤ levels + 1)).trans hmax)
    exact (Int.ofNat_le.mpr hh).trans hmaxWord
  have hproducts (i : ℕ) (hi : i < levels) : ∀ j < s, ∀ k < s, qs i * primes j * primes k ≤ maxMod :=
    by
    intro j hj k hk
    calc
      _ ≤ Y ^ i * Y * Y := Nat.mul_le_mul (Nat.mul_le_mul (hqhi i) (hhi j hj)) (hhi k hk)
      _ = Y ^ (i + 2) := by simp [pow_succ]
      _ ≤ Y ^ (levels + 1) := (Nat.pow_le_pow_right hY (by omega))
      _ ≤ maxMod := hmax
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
    refine _root_.Light.Ends.setToThen 1 ?_ ?_ ?_
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
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen (free + levels + 1) ?_ ?_ ?_
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
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.storeToThen free (1 : ℕ) ?_ ?_ ?_
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
      (Ends.for (T := levels * (ct + 100) + 20) (Q := Inv μ qs a b c nA nB nC N aux s levels free levels)
        (Inv μ qs a b c nA nB nC N aux s levels free) levels (ct + 80) ?_ ?_ ?_ ?_ (hT := by
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
  · refine ⟨0, Function.update μ free (1 : ℤ), ?_, ?_, ?_⟩
    · simp [qs, modulus, update_frame_setLocal]
    · intro j hj
      have hj0 : j = 0 := by omega
      simp [hj0, qs, modulus]
    · intro j hj
      exact Function.update_of_ne (by omega) _ _
  · rintro i _ hi _ ⟨pval, ν, rfl, hwritten, hkept⟩
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
      |
        refine
          _root_.Light.Ends.callToThen
            ((S.minimum.meets (d := d + 1) (q := qs i) (free := free + levels + 1) primes hw (hqpos i) hs (by omega)
                (by omega) (by omega) (by omega) hnA hnB hnC hspace hword (by omega) hAν hBν hCν hreadν hprime hinj
                (hproducts i hi))
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          _root_.Light.Ends.callToThen
            (S.minimum.meets (d := d + 1) (q := qs i) (free := free + levels + 1) primes hw (hqpos i) hs (by omega)
              (by omega) (by omega) (by omega) hnA hnB hnC hspace hword (by omega) hAν hBν hCν hreadν hprime hinj
              (hproducts i hi))
            ?_ ?_ ?_ ?_
      on_goal -1 =>
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
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ct] <;> omega)
      on_goal -1 => (rintro result ν₁ ⟨hresult, hkeep₁⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    have hchosen :
      chosenPrime primes s (qs i) nA nB nC (fun j => ν (a + j)) (fun j => ν (b + j)) (fun j => ν (c + j)) =
        chosenPrime primes s (qs i) nA nB nC A B C :=
      chosenPrime_congr (fun j hj => hkept _ (by omega)) (fun j hj => hkept _ (by omega))
        (fun j hj => hkept _ (by omega))
    rw [hchosen] at hresult
    subst result
    have hnext := hqWord (i + 1) (by omega)
    have hprodWord : (qs i : ℤ) * (chosenPrime primes s (qs i) nA nB nC A B C : ℤ) ≤ lim.word := by
      simpa only [qs, modulus, Nat.cast_mul] using hnext
    have hprodNonneg : (0 : ℤ) ≤ (qs i : ℤ) * (chosenPrime primes s (qs i) nA nB nC A B C : ℤ) := by positivity
    dsimp only [qs] at hprodWord hprodNonneg
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        (repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_))
      refine _root_.Light.Ends.setToThen (qs (i + 1)) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, qs, modulus, ct]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [qs, modulus, ct] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, qs, modulus, ct] <;> omega)
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
      refine _root_.Light.Ends.storeToThen (free + i + 1) (qs (i + 1)) ?_ ?_ ?_
      on_goal -1 =>
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
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ct] <;> omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    refine
      ⟨by simp, chosenPrime primes s (qs i) nA nB nC A B C, Function.update ν₁ (free + i + 1) (qs (i + 1) : ℤ), ?_, ?_,
        ?_⟩
    · simp [update_frame_setLocal]
    · intro j hj
      by_cases heq : j = i + 1
      · simp [heq, Nat.add_assoc]
      · rw [Function.update_of_ne (by omega)]
        exact (hkeep₁ _ (by omega)).trans (hwritten j (by omega))
    · intro j hj
      rw [Function.update_of_ne (by omega)]
      exact (hkeep₁ _ (by omega)).trans (hkept j hj)
  · intro σ _ hI
    exact hI
  · rintro i _ hi _ ⟨pval, ν, rfl, hwritten, hkept⟩
    simp
  · rintro σ ⟨pval, ν, rfl, hwritten, hkept⟩
    have hfinal := hqWord levels le_rfl
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        (repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_))
      refine _root_.Light.Ends.setToThen (qs levels) ?_ ?_ ?_
      on_goal -1 =>
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
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ct] <;> omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    exact ⟨by simp [qs, A, B, C], hwritten, hkept⟩
end Procs
end ThreeSum.LightPrimeChain
