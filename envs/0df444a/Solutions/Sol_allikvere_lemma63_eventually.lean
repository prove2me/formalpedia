-- Prove2me | solution 1 for allikvere_lemma63_eventually
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-10T10:55:30.393813+00:00
-- url     : https://prove2.me/submissions/c9b0bbf7-5a4a-494e-a944-dc5587c899e3

/- Standalone producer for Allikvere Lemma 6.3.

The core stopping-set definitions are imported from the definition-module
interface.  The remaining checked proof closure is inlined below.
-/
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic
import Definitions.Def_syracuseStep
import Definitions.Def_allikvere_stopping_set

set_option autoImplicit false
open Nat
open scoped BigOperators
noncomputable section


set_option autoImplicit false

open Nat

private lemma two_dvd_three_mul_add_one_of_odd {n : ℕ} (hn : Odd n) :
    2 ∣ 3 * n + 1 := by
  obtain ⟨k, hk⟩ := hn
  rw [hk]
  refine ⟨3 * k + 2, ?_⟩
  omega

/-- Every positive Syracuse successor is positive. -/
theorem syracuse_step_pos {n : ℕ} (hn : 0 < n) : 0 < syracuseStep n := by
  have hpos : 0 < 3 * n + 1 := by omega
  apply Nat.ordCompl_pos
  exact hpos.ne'

/-- Every positive Syracuse successor is odd. -/
theorem syracuse_step_odd {n : ℕ} (hn : 0 < n) : Odd (syracuseStep n) := by
  have hpos : 0 < 3 * n + 1 := by omega
  have hcop : Nat.Coprime 2 (ordCompl[2] (3 * n + 1)) :=
    Nat.coprime_ordCompl Nat.prime_two hpos.ne'
  exact hcop.odd_of_left

/-- An odd positive input has a positive 2-adic exponent in its Syracuse numerator. -/
theorem syracuse_step_factorization_pos {n : ℕ} (hn : 0 < n) (hodd : Odd n) :
    0 < (3 * n + 1).factorization 2 := by
  have hpos : 0 < 3 * n + 1 := by omega
  apply Nat.Prime.factorization_pos_of_dvd Nat.prime_two
  · exact hpos.ne'
  · exact two_dvd_three_mul_add_one_of_odd hodd

/-- The valuation-weighted Syracuse recurrence. -/
theorem syracuse_step_factorization_mul {n : ℕ} :
    2 ^ ((3 * n + 1).factorization 2) * syracuseStep n = 3 * n + 1 := by
  simpa [syracuseStep] using Nat.ordProj_mul_ordCompl_eq_self (3 * n + 1) 2

/- The three adapter facts are often consumed together on positive odd inputs. -/
theorem syracuse_step_pos_odd_valuation {n : ℕ} (hn : 0 < n) (hodd : Odd n) :
    0 < syracuseStep n ∧ Odd (syracuseStep n) ∧
      0 < (3 * n + 1).factorization 2 ∧
        2 ^ ((3 * n + 1).factorization 2) * syracuseStep n = 3 * n + 1 := by
  exact ⟨syracuse_step_pos hn, syracuse_step_odd hn,
    syracuse_step_factorization_pos hn hodd, syracuse_step_factorization_mul⟩


set_option autoImplicit false

open scoped BigOperators

/-- The exact exponent used by the `i`-th accelerated Syracuse step. -/
def syracuseExponent (N i : ℕ) : ℕ :=
  (3 * (syracuseStep^[i]) N + 1).factorization 2

/-- Positive oddness propagates through every forward Syracuse iterate. -/
theorem syracuse_iterate_pos_odd (N : ℕ) (hN : 0 < N) (hodd : Odd N) (i : ℕ) :
    0 < (syracuseStep^[i]) N ∧ Odd ((syracuseStep^[i]) N) := by
  induction i with
  | zero =>
      simpa using And.intro hN hodd
  | succ i ih =>
      rw [Function.iterate_succ_apply']
      exact ⟨syracuse_step_pos ih.1, syracuse_step_odd ih.1⟩

/-- Every exponent in the positive odd Syracuse orbit is positive. -/
theorem syracuse_exponent_pos (N i : ℕ) (hN : 0 < N) (hodd : Odd N) :
    0 < syracuseExponent N i := by
  unfold syracuseExponent
  obtain ⟨hi_pos, hi_odd⟩ := syracuse_iterate_pos_odd N hN hodd i
  exact syracuse_step_factorization_pos hi_pos hi_odd

/-- Each consecutive pair in the orbit satisfies the exact valuation recurrence. -/
theorem syracuse_exponent_chain (N i : ℕ) :
    2 ^ syracuseExponent N i * (syracuseStep^[i + 1]) N =
      3 * (syracuseStep^[i]) N + 1 := by
  simpa [syracuseExponent, Function.iterate_succ_apply'] using
    (syracuse_step_factorization_mul (n := (syracuseStep^[i]) N))

/-- A positive threshold crossed by a finite partial sum has a first crossing. -/
theorem exists_first_crossing (a : ℕ → ℕ) :
    ∀ (t q : ℕ), 0 < q → q ≤ ∑ i ∈ Finset.range t, a i →
      ∃ k < t,
        (∑ i ∈ Finset.range k, a i) < q ∧
          q ≤ (∑ i ∈ Finset.range k, a i) + a k
  | 0, q, hq, hsum => by
      simp at hsum
      omega
  | t + 1, q, hq, hsum => by
      by_cases hprefix : q ≤ ∑ i ∈ Finset.range t, a i
      · obtain ⟨k, hkt, hlt, hcross⟩ := exists_first_crossing a t q hq hprefix
        exact ⟨k, lt_trans hkt (Nat.lt_succ_self t), hlt, hcross⟩
      · have hlt : (∑ i ∈ Finset.range t, a i) < q := Nat.lt_of_not_ge hprefix
        refine ⟨t, Nat.lt_succ_self t, hlt, ?_⟩
        simpa [Finset.sum_range_succ] using hsum


set_option autoImplicit false

open Nat

/-- Exactness of the exponent in `3 * n + 1` is equivalent to an odd
quotient, not merely to divisibility by the corresponding power of two. -/
theorem syracuse_factorization_two_iff_odd_quotient (n a : ℕ) :
    (3 * n + 1).factorization 2 = a ↔
      ∃ m : ℕ, Odd m ∧ 2 ^ a * m = 3 * n + 1 := by
  have hpos : 0 < 3 * n + 1 := by omega
  constructor
  · intro ha
    have hcop : Nat.Coprime 2 (ordCompl[2] (3 * n + 1)) :=
      Nat.coprime_ordCompl Nat.prime_two hpos.ne'
    refine ⟨syracuseStep n, ?_, ?_⟩
    · simpa [syracuseStep] using hcop.odd_of_left
    · simpa [ha] using (syracuse_step_factorization_mul (n := n))
  · rintro ⟨m, hmodd, hmul⟩
    have hpowdvd : 2 ^ a ∣ 3 * n + 1 := ⟨m, hmul.symm⟩
    have hle : a ≤ (3 * n + 1).factorization 2 := by
      exact (Nat.prime_two.pow_dvd_iff_le_factorization hpos.ne').mp hpowdvd
    have hnotdvd : ¬2 ^ (a + 1) ∣ 3 * n + 1 := by
      intro hdiv
      rcases hdiv with ⟨k, hk⟩
      have hcancel : 2 * k = m := by
        apply Nat.mul_left_cancel (Nat.pow_pos (by decide : 0 < 2) : 0 < 2 ^ a)
        calc
          2 ^ a * (2 * k) = 2 ^ (a + 1) * k := by
            simp [pow_succ, Nat.mul_assoc]
          _ = 3 * n + 1 := hk.symm
          _ = 2 ^ a * m := hmul.symm
      obtain ⟨j, hj⟩ := hmodd
      omega
    have hnotle : ¬a + 1 ≤ (3 * n + 1).factorization 2 := by
      intro h
      apply hnotdvd
      exact (Nat.prime_two.pow_dvd_iff_le_factorization hpos.ne').mpr h
    omega


set_option autoImplicit false

open Nat
open scoped BigOperators

/- The affine numerator is kept in a form whose head/tail decomposition is
   immediate.  For `as = [a₀, ..., aₖ]`, it equals
   `3^as.length * N` plus the usual weighted prefix-power constant. -/
def syracuseAffineConstant : List ℕ → ℕ
  | [] => 0
  | a :: as => 3 ^ as.length + 2 ^ a * syracuseAffineConstant as

def syracuseAffineNumerator (as : List ℕ) (N : ℕ) : ℕ :=
  3 ^ as.length * N + syracuseAffineConstant as

def syracuseExactValuationPrefix (N : ℕ) : List ℕ → Prop
  | [] => True
  | a :: as => syracuseExponent N 0 = a ∧
      syracuseExactValuationPrefix (syracuseStep N) as

lemma syracuseAffineNumerator_shift (as : List ℕ) (N : ℕ) :
    syracuseAffineNumerator as N =
      3 ^ as.length * N + syracuseAffineNumerator as 0 := by
  simp [syracuseAffineNumerator]

lemma syracuseAffineNumerator_cons (a : ℕ) (as : List ℕ) (N : ℕ) :
    syracuseAffineNumerator (a :: as) N =
      3 ^ as.length * (3 * N + 1) +
        2 ^ a * syracuseAffineNumerator as 0 := by
  simp [syracuseAffineNumerator, syracuseAffineConstant, pow_succ]
  ring

lemma syracuseAffineConstant_cons_odd (a : ℕ) (as : List ℕ) (ha : 0 < a) :
    Odd (syracuseAffineConstant (a :: as)) := by
  simp only [syracuseAffineConstant]
  apply Odd.add_even
  · exact Odd.pow (by decide : Odd (3 : ℕ))
  · exact ((show Even (2 : ℕ) from ⟨1, by omega⟩).pow_of_ne_zero
      (by omega : a ≠ 0)).mul_right _

lemma syracuse_exponent_step_shift (N i : ℕ) :
    syracuseExponent (syracuseStep N) i = syracuseExponent N (i + 1) := by
  simp only [syracuseExponent]
  rw [← Function.iterate_succ_apply, Function.iterate_succ_apply']

theorem syracuse_exact_valuation_prefix_iff
    (N : ℕ) (hN : 0 < N) (hodd : Odd N) (as : List ℕ)
    (ha : ∀ a ∈ as, 0 < a) :
    syracuseExactValuationPrefix N as ↔
      ∃ m : ℕ, Odd m ∧
        2 ^ as.sum * m = syracuseAffineNumerator as N := by
  induction as generalizing N with
  | nil =>
      constructor
      · intro _
        exact ⟨N, hodd, by simp [syracuseAffineNumerator, syracuseAffineConstant]⟩
      · rintro ⟨m, hm, _⟩
        trivial
  | cons a as ih =>
      have ha0 : 0 < a := ha a (by simp)
      have harest : ∀ b ∈ as, 0 < b := by
        intro b hb
        exact ha b (by simp [hb])
      constructor
      · rintro ⟨hhead, htail⟩
        have hstep_pos : 0 < syracuseStep N := syracuse_step_pos hN
        have hstep_odd : Odd (syracuseStep N) := syracuse_step_odd hN
        obtain ⟨m, hm, htailEq⟩ :=
          (ih (N := syracuseStep N) hstep_pos hstep_odd harest).mp htail
        have hchain : 2 ^ a * syracuseStep N = 3 * N + 1 := by
          calc
            2 ^ a * syracuseStep N =
                2 ^ syracuseExponent N 0 * syracuseStep N := by rw [hhead]
            _ = 3 * N + 1 := by simpa using syracuse_exponent_chain N 0
        refine ⟨m, hm, ?_⟩
        calc
          2 ^ (a :: as).sum * m =
              2 ^ a * (2 ^ as.sum * m) := by
                simp [List.sum_cons, pow_add]
                ring
          _ = 2 ^ a * syracuseAffineNumerator as (syracuseStep N) := by
                rw [htailEq]
          _ = 2 ^ a *
                (3 ^ as.length * syracuseStep N +
                  syracuseAffineNumerator as 0) := by
                rw [syracuseAffineNumerator_shift]
          _ = 3 ^ as.length * (3 * N + 1) +
                2 ^ a * syracuseAffineNumerator as 0 := by
                rw [← hchain]
                ring
          _ = syracuseAffineNumerator (a :: as) N := by
                symm
                exact syracuseAffineNumerator_cons a as N
      · rintro ⟨m, hm, hEq⟩
        have hEq' :
            2 ^ (a + as.sum) * m = syracuseAffineNumerator (a :: as) N := by
          simpa [List.sum_cons] using hEq
        let x : ℕ := 2 ^ as.sum * m
        have hAeq : syracuseAffineNumerator (a :: as) N = 2 ^ a * x := by
          calc
            syracuseAffineNumerator (a :: as) N = 2 ^ (a + as.sum) * m := hEq'.symm
            _ = 2 ^ a * x := by
              simp [x, pow_add]
              ring
        have hAdiv : 2 ^ a ∣ syracuseAffineNumerator (a :: as) N :=
          ⟨x, hAeq⟩
        have hsumdiv :
            2 ^ a ∣ 3 ^ as.length * (3 * N + 1) +
              2 ^ a * syracuseAffineNumerator as 0 := by
          rw [syracuseAffineNumerator_cons] at hAdiv
          exact hAdiv
        have hCdiv : 2 ^ a ∣ 2 ^ a * syracuseAffineNumerator as 0 :=
          dvd_mul_right _ _
        have hsumdiv' :
            2 ^ a ∣ 2 ^ a * syracuseAffineNumerator as 0 +
              3 ^ as.length * (3 * N + 1) := by
          simpa [Nat.add_comm] using hsumdiv
        have hXdiv : 2 ^ a ∣ 3 ^ as.length * (3 * N + 1) := by
          simpa using (Nat.dvd_add_iff_right hCdiv).mpr hsumdiv'
        have hcop : Nat.Coprime (2 ^ a) (3 ^ as.length) := by
          exact Nat.Coprime.pow _ _ (by decide : Nat.Coprime 2 3)
        have hheadDiv : 2 ^ a ∣ 3 * N + 1 :=
          (hcop.dvd_mul_left).mp hXdiv
        obtain ⟨y, hy⟩ := hheadDiv
        have hy_pos : 0 < y := by
          have hy_ne : y ≠ 0 := by
            intro hy0
            subst y
            simp at hy
          exact Nat.pos_of_ne_zero hy_ne
        have hrel : x = 3 ^ as.length * y + syracuseAffineNumerator as 0 := by
          apply Nat.mul_left_cancel (Nat.pow_pos (by decide : 0 < 2) : 0 < 2 ^ a)
          calc
            2 ^ a * x = syracuseAffineNumerator (a :: as) N := hAeq.symm
            _ = 3 ^ as.length * (3 * N + 1) +
                2 ^ a * syracuseAffineNumerator as 0 :=
                  syracuseAffineNumerator_cons a as N
            _ = 3 ^ as.length * (2 ^ a * y) +
                2 ^ a * syracuseAffineNumerator as 0 := by rw [hy]
            _ = 2 ^ a *
                (3 ^ as.length * y + syracuseAffineNumerator as 0) := by
                  ring
        have hy_odd : Odd y := by
          cases as with
          | nil =>
              have hy_eq : y = m := by
                calc
                  y = x := by
                    simpa [syracuseAffineNumerator, syracuseAffineConstant] using hrel.symm
                  _ = m := by simp [x]
              simpa [hy_eq] using hm
          | cons b bs =>
              have hb : 0 < b := harest b (by simp)
              have hsum_pos : 0 < (b :: bs).sum := by
                simp [List.sum_cons]
                omega
              have hx_even : Even x := by
                have hp : Even (2 ^ (b :: bs).sum) :=
                  (show Even (2 : ℕ) from ⟨1, by omega⟩).pow_of_ne_zero
                    (by omega : (b :: bs).sum ≠ 0)
                exact hp.mul_right m
              have hCodd : Odd (syracuseAffineConstant (b :: bs)) :=
                syracuseAffineConstant_cons_odd b bs hb
              have hCodd' : Odd (syracuseAffineNumerator (b :: bs) 0) := by
                simpa [syracuseAffineNumerator] using hCodd
              have hadd_even :
                  Even (3 ^ (b :: bs).length * y +
                    syracuseAffineNumerator (b :: bs) 0) := by
                rw [← hrel]
                exact hx_even
              have hprod_odd : Odd (3 ^ (b :: bs).length * y) :=
                (even_add').mp hadd_even |>.mpr hCodd'
              exact hprod_odd.of_mul_right
        have hhead : syracuseExponent N 0 = a := by
          simpa [syracuseExponent] using
            (syracuse_factorization_two_iff_odd_quotient N a).mpr
              ⟨y, hy_odd, hy.symm⟩
        have hy_step : y = syracuseStep N := by
          apply Nat.mul_left_cancel (Nat.pow_pos (by decide : 0 < 2) : 0 < 2 ^ a)
          calc
            2 ^ a * y = 3 * N + 1 := hy.symm
            _ = 2 ^ a * syracuseStep N := by
              rw [← hhead]
              simpa using (syracuse_exponent_chain N 0).symm
        have htailEq :
            2 ^ as.sum * m = syracuseAffineNumerator as y := by
          calc
            2 ^ as.sum * m = x := by rfl
            _ = 3 ^ as.length * y + syracuseAffineNumerator as 0 := hrel
            _ = syracuseAffineNumerator as y :=
              (syracuseAffineNumerator_shift as y).symm
        have htail :=
          (ih (N := y) hy_pos hy_odd harest).mpr ⟨m, hm, htailEq⟩
        exact ⟨hhead, by simpa [hy_step] using htail⟩

/-- Finite-function adapter for the list-inductive characterization. -/
theorem syracuse_exact_valuation_prefix_fin_iff
    (N t : ℕ) (hN : 0 < N) (hodd : Odd N)
    (a : Fin t → ℕ) (ha : ∀ i, 0 < a i) :
    syracuseExactValuationPrefix N (List.ofFn a) ↔
      ∃ m : ℕ, Odd m ∧
        2 ^ (∑ i, a i) * m = syracuseAffineNumerator (List.ofFn a) N := by
  have hlist : ∀ b ∈ List.ofFn a, 0 < b := by
    rw [List.forall_mem_ofFn_iff]
    exact ha
  have h := syracuse_exact_valuation_prefix_iff N hN hodd (List.ofFn a) hlist
  simpa [List.sum_ofFn] using h


/- These two exact-prefix index predicates are proof-local helpers rather
than part of the definition-module interface. -/
def allikvereEPrimePrefix (x : ℝ)
    (a : Fin (allikvereM0 x) → ℕ) : Set ℕ :=
  {M | M ∈ allikvereEPrime x ∧
    syracuseExactValuationPrefix M (List.ofFn a)}

def allikvereAdmissiblePrefix (x : ℝ)
    (a : Fin (allikvereM0 x) → ℕ) : Prop :=
  (∀ i, 0 < a i) ∧
    ∃ M, M ∈ allikvereEPrime x ∧
      syracuseExactValuationPrefix M (List.ofFn a)


set_option autoImplicit false

open Nat
open scoped BigOperators

/- An odd quotient is exactly the residue `2^S` modulo the next power of two. -/
theorem odd_quotient_iff_modEq_pow_two (A S : ℕ) :
    (∃ m : ℕ, Odd m ∧ 2 ^ S * m = A) ↔
      Nat.ModEq (2 ^ (S + 1)) A (2 ^ S) := by
  constructor
  · rintro ⟨m, hm, rfl⟩
    obtain ⟨q, hq⟩ := hm
    rw [hq]
    have hle : 2 ^ S ≤ 2 ^ S * (2 * q + 1) := by
      have hp : 0 < 2 ^ S := Nat.pow_pos (by decide)
      nlinarith
    have hdvd : 2 ^ (S + 1) ∣ 2 ^ S * (2 * q + 1) - 2 ^ S := by
      refine ⟨q, ?_⟩
      rw [pow_succ]
      ring_nf
      omega
    exact (Nat.modEq_iff_dvd' hle).mpr hdvd |>.symm
  · intro h
    have hpow : 2 ^ S < 2 ^ (S + 1) := by
      rw [pow_succ]
      have hp : 0 < 2 ^ S := Nat.pow_pos (by decide)
      omega
    have hrem : A % 2 ^ (S + 1) = 2 ^ S := by
      simpa [Nat.ModEq, Nat.mod_eq_of_lt hpow] using h
    have hdecomp := Nat.mod_add_div A (2 ^ (S + 1))
    refine ⟨2 * (A / 2 ^ (S + 1)) + 1, ?_, ?_⟩
    · exact ⟨A / 2 ^ (S + 1), by omega⟩
    · rw [hrem] at hdecomp
      calc
        2 ^ S * (2 * (A / 2 ^ (S + 1)) + 1) =
            2 ^ S + 2 ^ (S + 1) * (A / 2 ^ (S + 1)) := by
              rw [pow_succ]
              ring
        _ = A := hdecomp

private lemma syracuse_affine_coefficient_coprime (t S : ℕ) :
    Nat.Coprime (2 ^ (S + 1)) (3 ^ t) := by
  exact Nat.Coprime.pow _ _ (by decide : Nat.Coprime 2 3)

private lemma affine_residue_exists (t S C : ℕ) :
    ∃ r : Fin (2 ^ (S + 1)),
      Nat.ModEq (2 ^ (S + 1)) (3 ^ t * r.val + C) (2 ^ S) := by
  let M : ℕ := 2 ^ (S + 1)
  have hM : 0 < M := by
    dsimp [M]
    exact Nat.pow_pos (by decide)
  haveI : NeZero M := ⟨hM.ne'⟩
  let u : (ZMod M)ˣ := ZMod.unitOfCoprime (3 ^ t)
    (by simpa [M] using (syracuse_affine_coefficient_coprime t S).symm)
  let z : ZMod M := (u⁻¹ : ZMod M) * ((2 ^ S : ZMod M) - (C : ZMod M))
  let r : Fin M := ⟨z.val, ZMod.val_lt z⟩
  refine ⟨r, ?_⟩
  apply (ZMod.natCast_eq_natCast_iff _ _ M).mp
  dsimp [r, z]
  rw [Nat.cast_add, Nat.cast_mul, ZMod.natCast_zmod_val]
  have hu : (u : ZMod M) = 3 ^ t := by
    simp [u]
  have hu' : ((3 ^ t : ℕ) : ZMod M) = (u : ZMod M) := by simpa using hu.symm
  rw [hu']
  simp

private lemma affine_modEq_iff_residue
    (t S C : ℕ) (r : Fin (2 ^ (S + 1)))
    (hr : Nat.ModEq (2 ^ (S + 1)) (3 ^ t * r.val + C) (2 ^ S))
    (N : ℕ) :
    Nat.ModEq (2 ^ (S + 1)) (3 ^ t * N + C) (2 ^ S) ↔
      N % 2 ^ (S + 1) = r.val := by
  have hcop : Nat.Coprime (2 ^ (S + 1)) (3 ^ t) :=
    syracuse_affine_coefficient_coprime t S
  constructor
  · intro hN
    have hmul : Nat.ModEq (2 ^ (S + 1)) (3 ^ t * N) (3 ^ t * r.val) := by
      exact Nat.ModEq.add_right_cancel' C (hN.trans hr.symm)
    have hcancel := Nat.ModEq.cancel_left_of_coprime hcop hmul
    simpa [Nat.ModEq, Nat.mod_eq_of_lt r.isLt] using hcancel
  · intro hN
    have hNr : Nat.ModEq (2 ^ (S + 1)) N r.val := by
      simpa [Nat.ModEq, Nat.mod_eq_of_lt r.isLt] using hN
    exact (Nat.ModEq.mul_left (3 ^ t) hNr).add_right C |>.trans hr

private lemma affine_constant_odd_of_pos
    (as : List ℕ) (hpos : ∀ b ∈ as, 0 < b) (hne : as ≠ []) :
    Odd (syracuseAffineConstant as) := by
  cases as with
  | nil => contradiction
  | cons b bs =>
      exact syracuseAffineConstant_cons_odd b bs (hpos b (by simp))

theorem syracuse_exact_prefix_residue
    (t : ℕ) (a : Fin t → ℕ) (ha : ∀ i, 0 < a i) :
    ∃ r : Fin (2 ^ ((∑ i, a i) + 1)),
      Odd r.val ∧
      ∀ N : ℕ, 0 < N → Odd N →
        (syracuseExactValuationPrefix N (List.ofFn a) ↔
          N % 2 ^ ((∑ i, a i) + 1) = r.val) := by
  by_cases ht : t = 0
  · subst t
    have hsum : ∑ i, a i = 0 := by simp
    have hrbound : 1 < 2 ^ ((∑ i, a i) + 1) := by
      rw [hsum]
      decide
    let r : Fin (2 ^ ((∑ i, a i) + 1)) := ⟨1, hrbound⟩
    refine ⟨r, ?_, ?_⟩
    · change Odd 1
      exact ⟨0, by omega⟩
    · exact fun N hN hodd ↦ by
        constructor
        · intro _
          obtain ⟨k, hk⟩ := hodd
          simp only [Finset.univ_eq_empty, Finset.sum_empty, Nat.zero_add, pow_one] at *
          simp [r, hk]
        · intro _
          trivial
  · have htpos : 0 < t := Nat.pos_of_ne_zero ht
    let S : ℕ := ∑ i, a i
    let C : ℕ := syracuseAffineConstant (List.ofFn a)
    obtain ⟨r, hr⟩ := affine_residue_exists t S C
    have hS : 0 < S := by
      dsimp [S]
      exact Finset.sum_pos' (fun i _ => Nat.zero_le _) ⟨⟨0, htpos⟩, Finset.mem_univ _, ha _⟩
    have hCodd : Odd C := by
      have hposlist : ∀ b ∈ List.ofFn a, 0 < b := by
        rw [List.forall_mem_ofFn_iff]
        exact ha
      have hne : (List.ofFn a).length ≠ 0 := by simp [ht]
      have hne' : List.ofFn a ≠ [] := by simpa using hne
      dsimp [C]
      exact affine_constant_odd_of_pos (List.ofFn a) hposlist hne'
    have hrodd : Odd r.val := by
      obtain ⟨m, hm, hEq⟩ :=
        (odd_quotient_iff_modEq_pow_two (3 ^ t * r.val + C) S).mpr hr
      have hEven : Even (3 ^ t * r.val + C) := by
        rw [← hEq]
        exact ((show Even (2 : ℕ) from ⟨1, by omega⟩).pow_of_ne_zero
          (by omega : S ≠ 0)).mul_right m
      have hprod : Odd (3 ^ t * r.val) := (even_add').mp hEven |>.mpr hCodd
      exact hprod.of_mul_right
    refine ⟨r, hrodd, ?_⟩
    exact fun N hN hodd ↦ by
      have hprefix :
          syracuseExactValuationPrefix N (List.ofFn a) ↔
            ∃ m : ℕ, Odd m ∧ 2 ^ S * m = 3 ^ t * N + C := by
        rw [syracuse_exact_valuation_prefix_fin_iff N t hN hodd a ha]
        simp [S, C, syracuseAffineNumerator, List.length_ofFn]
      rw [hprefix, odd_quotient_iff_modEq_pow_two]
      exact affine_modEq_iff_residue t S C r hr N


set_option autoImplicit false

open Nat

/- The recursive list predicate from the affine-prefix proof is exactly the
   coordinate-wise assertion on the corresponding finite tuple. -/
theorem syracuse_exact_prefix_coordinates
    (N t : ℕ) (a : Fin t → ℕ) (hN : 0 < N) (hodd : Odd N)
    (ha : ∀ i, 0 < a i) :
    syracuseExactValuationPrefix N (List.ofFn a) ↔
      ∀ i : Fin t, syracuseExponent N i = a i := by
  induction t generalizing N with
  | zero =>
      simp [syracuseExactValuationPrefix]
  | succ t ih =>
      let tail : Fin t → ℕ := fun i => a i.succ
      have htail_pos : ∀ i, 0 < tail i := by
        intro i
        exact ha i.succ
      have haeq : a = Fin.cons (a 0) tail := by
        funext i
        exact Fin.cases rfl (fun j => rfl) i
      rw [haeq, List.ofFn_cons]
      have hstep_pos : 0 < syracuseStep N := syracuse_step_pos hN
      have hstep_odd : Odd (syracuseStep N) := syracuse_step_odd hN
      have ihstep :
          syracuseExactValuationPrefix (syracuseStep N) (List.ofFn tail) ↔
            ∀ i : Fin t, syracuseExponent (syracuseStep N) i = tail i :=
        ih (N := syracuseStep N) (a := tail) hstep_pos hstep_odd htail_pos
      constructor
      · rintro ⟨hhead, htail⟩ i
        refine Fin.cases hhead (fun j => ?_) i
        have hj' := (ihstep.mp htail) j
        rw [syracuse_exponent_step_shift] at hj'
        exact hj'
      · intro hcoords
        refine ⟨hcoords 0, ?_⟩
        apply ihstep.mpr
        intro j
        have hj := hcoords j.succ
        rw [syracuse_exponent_step_shift]
        simpa using hj

theorem syracuse_exact_prefix_coordinates_residue
    (t : ℕ) (a : Fin t → ℕ) (ha : ∀ i, 0 < a i) :
    ∃ r : Fin (2 ^ ((∑ i, a i) + 1)),
      Odd r.val ∧
      ∀ N : ℕ, 0 < N → Odd N →
        ((∀ i : Fin t, syracuseExponent N i = a i) ↔
          N % 2 ^ ((∑ i, a i) + 1) = r.val) := by
  obtain ⟨r, hr, hres⟩ := syracuse_exact_prefix_residue t a ha
  refine ⟨r, hr, ?_⟩
  intro N hN hodd
  rw [← syracuse_exact_prefix_coordinates N t a hN hodd ha]
  exact hres N hN hodd


/-
  Counting positive exponent prefixes.

  The finite cut set is not used as a substitute for the exponent tuples: the
  first part below gives an explicit composition map from the bounded tuples to
  positive compositions, and the second part identifies fixed-length
  compositions with their interior cuts.
-/


open scoped BigOperators

def PositiveExponentPrefix (k n' : ℕ) :=
  {a : Fin k → Fin n' // (∀ i, 0 < (a i).val) ∧ (∑ i, (a i).val) < n'}

def PositiveCompositionPrefix (k n' : ℕ) :=
  {c : Composition n' // c.length = k + 1}

instance positiveExponentPrefixFintype (k n' : ℕ) : Fintype (PositiveExponentPrefix k n') :=
  by
    classical
    unfold PositiveExponentPrefix
    infer_instance

instance positiveCompositionPrefixFintype (k n' : ℕ) : Fintype (PositiveCompositionPrefix k n') :=
  by
    classical
    unfold PositiveCompositionPrefix
    infer_instance

def tupleBlocks {k n' : ℕ} (a : PositiveExponentPrefix k n') : List ℕ :=
  List.ofFn (fun i : Fin k => (a.1 i).val) ++ [n' - ∑ i, (a.1 i).val]

private lemma tupleBlocks_length {k n' : ℕ} (a : PositiveExponentPrefix k n') :
    (tupleBlocks a).length = k + 1 := by
  simp [tupleBlocks]

private lemma tupleBlocks_sum {k n' : ℕ} (a : PositiveExponentPrefix k n') :
    (tupleBlocks a).sum = n' := by
  have hle : (∑ i, (a.1 i).val) ≤ n' := Nat.le_of_lt a.2.2
  simp only [tupleBlocks, List.sum_append, List.sum_singleton, List.sum_ofFn]
  exact Nat.add_sub_of_le hle

private lemma tupleBlocks_pos {k n' : ℕ} (a : PositiveExponentPrefix k n') :
    ∀ {x}, x ∈ tupleBlocks a → 0 < x := by
  intro x hx
  simp only [tupleBlocks, List.mem_append, List.mem_singleton] at hx
  rcases hx with hx | rfl
  · rcases List.mem_ofFn.mp hx with ⟨i, rfl⟩
    exact a.2.1 i
  · have hlt := a.2.2
    omega

def tupleToComposition {k n' : ℕ} (a : PositiveExponentPrefix k n') : Composition n' :=
  { blocks := tupleBlocks a
    blocks_pos := tupleBlocks_pos a
    blocks_sum := tupleBlocks_sum a }

private lemma tupleToComposition_length {k n' : ℕ} (a : PositiveExponentPrefix k n') :
    (tupleToComposition a).length = k + 1 := by
  exact tupleBlocks_length a

private lemma tupleToComposition_block {k n' : ℕ} (a : PositiveExponentPrefix k n')
    (i : Fin k) :
    (tupleToComposition a).blocksFun ⟨i.1, by rw [tupleToComposition_length a]; omega⟩ =
      (a.1 i).val := by
  simp [tupleToComposition, tupleBlocks, Composition.blocksFun]

private lemma composition_index {k n' : ℕ} (c : PositiveCompositionPrefix k n')
    (i : Fin k) : i.1 < c.1.length := by
  rw [c.2]
  exact Nat.lt_succ_of_lt i.isLt

private lemma composition_positive {k n' : ℕ} (c : PositiveCompositionPrefix k n') :
    0 < n' := by
  have i0 : Fin c.1.length := ⟨0, by rw [c.2]; omega⟩
  have hsum := c.1.sum_blocksFun
  have hblock := c.1.one_le_blocksFun i0
  have hle : c.1.blocksFun i0 ≤ ∑ i : Fin c.1.length, c.1.blocksFun i :=
    Finset.single_le_sum (f := c.1.blocksFun) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i0)
  omega

private def compositionTuple {k n' : ℕ} (c : PositiveCompositionPrefix k n') :
  Fin k → Fin n' := fun i =>
  ⟨c.1.blocksFun ⟨i.1, composition_index c i⟩, by
    have hne : c.1 ≠ Composition.single n' (composition_positive c) := by
      intro h
      have hlen := c.2
      have hi := i.isLt
      rw [h, Composition.single_length] at hlen
      omega
    have hlt := (Composition.ne_single_iff (composition_positive c)).mp hne
      ⟨i.1, composition_index c i⟩
    omega⟩

private lemma compositionTuple_pos {k n' : ℕ} (c : PositiveCompositionPrefix k n') :
    ∀ i, 0 < (compositionTuple c i).val := by
  intro i
  exact lt_of_lt_of_le Nat.zero_lt_one (c.1.one_le_blocksFun ⟨i.1, composition_index c i⟩)

private lemma compositionTuple_sum_lt {k n' : ℕ} (_hn' : 0 < n')
    (c : PositiveCompositionPrefix k n') :
    (∑ i, (compositionTuple c i).val) < n' := by
  have hklen : k < c.1.length := by rw [c.2]; omega
  have hsum : (∑ i, (compositionTuple c i).val) = c.1.sizeUpTo k := by
    let g : Fin k → ℕ := fun i => c.1.blocksFun ⟨i.1, composition_index c i⟩
    have hlist : List.ofFn g = c.1.blocks.take k := by
      apply List.ext_getElem
      · simp [hklen.le]
      · intro i hi₁ hi₂
        simp [g, Composition.blocksFun]
    calc
      (∑ i, (compositionTuple c i).val) = (List.ofFn g).sum := by
        simp [g, compositionTuple, List.sum_ofFn]
      _ = (c.1.blocks.take k).sum := by rw [hlist]
      _ = c.1.sizeUpTo k := rfl
  rw [hsum]
  have hstrict := c.1.sizeUpTo_strict_mono hklen
  have hfull : c.1.sizeUpTo (k + 1) = n' := by
    simpa [c.2] using c.1.sizeUpTo_length
  omega

private def compositionToTuple {k n' : ℕ} (c : PositiveCompositionPrefix k n') :
    PositiveExponentPrefix k n' :=
  ⟨compositionTuple c, compositionTuple_pos c, compositionTuple_sum_lt (composition_positive c) c⟩

private lemma tupleToCompositionToTuple {k n' : ℕ} (a : PositiveExponentPrefix k n') :
    compositionToTuple ⟨tupleToComposition a, tupleToComposition_length a⟩ = a := by
  apply Subtype.ext
  funext i
  simp [compositionToTuple, compositionTuple, tupleToComposition_block]

private lemma compositionToTupleToComposition {k n' : ℕ} (c : PositiveCompositionPrefix k n') :
    tupleToComposition (compositionToTuple c) = c.1 := by
  apply Composition.ext
  apply List.ext_getElem
  · change (tupleToComposition (compositionToTuple c)).length = c.1.length
    calc
      (tupleToComposition (compositionToTuple c)).length = k + 1 :=
        tupleToComposition_length (compositionToTuple c)
      _ = c.1.length := c.2.symm
  · intro i hi₁ hi₂
    by_cases hki : i < k
    · let j : Fin k := ⟨i, hki⟩
      have hb := tupleToComposition_block (compositionToTuple c) j
      simpa [tupleBlocks, compositionToTuple, compositionTuple, Composition.blocksFun,
        hki, hi₁, hi₂, j] using hb
    · have hi₁' : i < k + 1 := by
        change i < (tupleToComposition (compositionToTuple c)).length at hi₁
        rw [tupleToComposition_length (compositionToTuple c)] at hi₁
        exact hi₁
      have hik : i = k := by omega
      subst i
      have hklen : k < c.1.length := by rw [c.2]; omega
      have hsum : ∑ i, ((compositionToTuple c).1 i).val = c.1.sizeUpTo k := by
        let g : Fin k → ℕ := fun i => c.1.blocksFun ⟨i.1, composition_index c i⟩
        have hlist : List.ofFn g = c.1.blocks.take k := by
          apply List.ext_getElem
          · simp [hklen.le]
          · intro j hj₁ hj₂
            simp [g, Composition.blocksFun]
        calc
          (∑ i, ((compositionToTuple c).1 i).val) = (List.ofFn g).sum := by
            simp [g, compositionToTuple, compositionTuple, List.sum_ofFn]
          _ = (c.1.blocks.take k).sum := by rw [hlist]
          _ = c.1.sizeUpTo k := rfl
      have hsize := c.1.sizeUpTo_succ hklen
      have hfull : c.1.sizeUpTo (k + 1) = n' := by
        simpa [c.2] using c.1.sizeUpTo_length
      rw [hfull] at hsize
      have hlast : c.1.blocks[k] = n' - ∑ i, ((compositionToTuple c).1 i).val := by
        omega
      calc
        (tupleToComposition (compositionToTuple c)).blocks[k] =
            n' - ∑ i, ((compositionToTuple c).1 i).val := by
              simp [tupleToComposition, tupleBlocks, List.getElem_append_right,
                List.length_ofFn]
        _ = c.1.blocks[k] := hlast.symm

private def tupleCompositionEquiv (k n' : ℕ) :
    PositiveExponentPrefix k n' ≃ PositiveCompositionPrefix k n' :=
  { toFun := fun a => ⟨tupleToComposition a, tupleToComposition_length a⟩
    invFun := compositionToTuple
    left_inv := tupleToCompositionToTuple
    right_inv := fun c => Subtype.ext (compositionToTupleToComposition c) }

private def InteriorCuts (k n' : ℕ) :=
  {s : Finset (Fin (n' - 1)) // s.card = k}

instance interiorCutsFintype (k n' : ℕ) : Fintype (InteriorCuts k n') := by
  classical
  unfold InteriorCuts
  infer_instance

private lemma inverse_composition_length {n' : ℕ} (hn' : 0 < n')
    (s : Finset (Fin (n' - 1))) :
    ((compositionAsSetEquiv n').symm s).length = s.card + 1 := by
  let sh : Fin (n' - 1) → Fin n'.succ := fun j => ⟨j.val + 1, by omega⟩
  have hsh : Function.Injective sh := by
    intro x y h
    apply Fin.ext
    have h' := congrArg Fin.val h
    dsimp [sh] at h'
    omega
  have himage : (s.image sh).card = s.card := by
    exact Finset.card_image_iff.mpr (Set.injOn_of_injective hsh)
  have h0 : (0 : Fin n'.succ) ∉ s.image sh := by
    simp only [Finset.mem_image]
    rintro ⟨j, hj, h⟩
    have h' := congrArg Fin.val h
    dsimp [sh] at h'
    omega
  have hlast : Fin.last n' ∉ s.image sh := by
    simp only [Finset.mem_image]
    rintro ⟨j, hj, h⟩
    have h' := congrArg Fin.val h
    dsimp [sh] at h'
    omega
  have h01 : (0 : Fin n'.succ) ≠ Fin.last n' := by
    intro h
    have h' := congrArg Fin.val h
    exact hn'.ne' h'.symm
  have hbound : ((compositionAsSetEquiv n').symm s).boundaries =
      insert 0 (insert (Fin.last n') (s.image sh)) := by
    dsimp [compositionAsSetEquiv]
    ext i
    simp only [Set.mem_toFinset, Finset.mem_insert, Finset.mem_image]
    constructor
    · rintro (rfl | rfl | ⟨j, hj, h⟩)
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr ⟨j, hj, by apply Fin.ext; dsimp [sh]; exact h.symm⟩)
    · rintro (rfl | rfl | ⟨j, hj, rfl⟩)
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr ⟨j, hj, rfl⟩)
  rw [CompositionAsSet.length, hbound]
  have h0' : (0 : Fin n'.succ) ∉ insert (Fin.last n') (s.image sh) := by
    simp [h01, h0]
  rw [Finset.card_insert_of_notMem h0', Finset.card_insert_of_notMem hlast, himage]
  omega

private lemma composition_cut_card {n' : ℕ} (hn' : 0 < n')
    (c : Composition n') :
    (compositionAsSetEquiv n' c.toCompositionAsSet).card = c.length - 1 := by
  let s := compositionAsSetEquiv n' c.toCompositionAsSet
  have h := inverse_composition_length hn' s
  have hleft : ((compositionAsSetEquiv n').symm s).length = c.length := by
    rw [show (compositionAsSetEquiv n').symm s = c.toCompositionAsSet by
      simp [s]]
    exact c.toCompositionAsSet_length
  have hs : s.card + 1 = c.length := by omega
  have hc : c.length = s.card + 1 := hleft.symm.trans h
  symm
  exact (Nat.sub_eq_iff_eq_add (by omega)).mpr hc

private def compositionCutsEquiv (k n' : ℕ) (hn' : 0 < n') :
    PositiveCompositionPrefix k n' ≃ InteriorCuts k n' := by
  let e : PositiveCompositionPrefix k n' → InteriorCuts k n' := fun c =>
    ⟨compositionAsSetEquiv n' c.1.toCompositionAsSet, by
      have h := composition_cut_card hn' c.1
      have hc := c.2
      omega⟩
  let f : InteriorCuts k n' → PositiveCompositionPrefix k n' := fun s =>
    ⟨((compositionAsSetEquiv n').symm s.1).toComposition, by
      have h := inverse_composition_length hn' s.1
      have hlen := CompositionAsSet.toComposition_length ((compositionAsSetEquiv n').symm s.1)
      have hs := s.2
      omega⟩
  exact
    { toFun := e
      invFun := f
      left_inv := by
        intro c
        apply Subtype.ext
        change ((compositionAsSetEquiv n').symm
          (compositionAsSetEquiv n' c.1.toCompositionAsSet)).toComposition = c.1
        rw [(compositionAsSetEquiv n').symm_apply_apply]
        exact (compositionEquiv n').left_inv c.1
      right_inv := by
        intro s
        apply Subtype.ext
        dsimp [e, f]
        change compositionAsSetEquiv n'
          (((compositionAsSetEquiv n').symm s.1).toComposition.toCompositionAsSet) = s.1
        rw [show ((compositionAsSetEquiv n').symm s.1).toComposition.toCompositionAsSet =
            ((compositionAsSetEquiv n').symm s.1) from
          (compositionEquiv n').right_inv ((compositionAsSetEquiv n').symm s.1)]
        exact (compositionAsSetEquiv n').apply_symm_apply s.1 }

theorem positive_exponent_prefix_card (k n' : ℕ) (hn' : 0 < n') :
    Fintype.card (PositiveExponentPrefix k n') = Nat.choose (n' - 1) k := by
  rw [Fintype.card_congr (tupleCompositionEquiv k n'),
    Fintype.card_congr (compositionCutsEquiv k n' hn')]
  simp [InteriorCuts]


/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under GPL-3.0-or-later as described in the file LICENSE.
Authors: Adam McKenna.
-/



set_option autoImplicit false

open scoped BigOperators

noncomputable section

/-!
# Generic bounded positive-prefix/last counting

This module is a finite combinatorial dependency for the later Allikvere consumer.
It contains no E′ predicate, Syracuse orbit estimate, source budget, probability
statement, or discrepancy claim.  The finite ambient product is explicit, so the
subtype has a genuine `Fintype` instance rather than relying on finiteness of
natural-valued functions.
-/

def AllikvereBoundedPrefixLast (k B V : ℕ) :=
  {a : Fin k.succ → Fin (max B V + 1) //
    (∀ i : Fin k, 0 < (a i.castSucc).val) ∧
      (∑ i : Fin k, (a i.castSucc).val) ≤ B ∧
      (a (Fin.last k)).val ≤ V}

instance allikvereBoundedPrefixLastFintype (k B V : ℕ) :
    Fintype (AllikvereBoundedPrefixLast k B V) := by
  classical
  unfold AllikvereBoundedPrefixLast
  infer_instance

private def allikvereBoundedPrefixLastEncode (k B V : ℕ)
    (a : AllikvereBoundedPrefixLast k B V) :
    PositiveExponentPrefix k (B + 1) × Fin (V + 1) :=
  (⟨fun i => ⟨(a.1 i.castSucc).val, by
      have hle : (a.1 i.castSucc).val ≤
          ∑ j : Fin k, (a.1 j.castSucc).val :=
        Finset.single_le_sum (f := fun j : Fin k => (a.1 j.castSucc).val)
          (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ i)
      have hsum : (∑ j : Fin k, (a.1 j.castSucc).val) ≤ B := a.2.2.1
      omega⟩,
    a.2.1,
    by
      change (∑ i : Fin k, (a.1 i.castSucc).val) < B + 1
      have hsum : (∑ i : Fin k, (a.1 i.castSucc).val) ≤ B := a.2.2.1
      omega⟩,
   ⟨(a.1 (Fin.last k)).val, by
      have hlast : (a.1 (Fin.last k)).val ≤ V := a.2.2.2
      omega⟩)

private lemma allikvereBoundedPrefixLastEncode_injective
    (k B V : ℕ) :
    Function.Injective (allikvereBoundedPrefixLastEncode k B V) := by
  intro a b hab
  apply Subtype.ext
  funext i
  rcases i.eq_castSucc_or_eq_last with ⟨j, rfl⟩ | rfl
  · have h := congrArg (fun p => (p.1.1 j).val) hab
    exact Fin.ext h
  · have h := congrArg (fun p => p.2.val) hab
    exact Fin.ext h

theorem allikvere_bounded_prefix_last_card_le_choose
    (k B V : ℕ) :
    Fintype.card (AllikvereBoundedPrefixLast k B V) ≤
      Nat.choose B k * (V + 1) := by
  let e := allikvereBoundedPrefixLastEncode k B V
  have hinj : Function.Injective e := by
    exact allikvereBoundedPrefixLastEncode_injective k B V
  calc
    Fintype.card (AllikvereBoundedPrefixLast k B V) ≤
        Fintype.card (PositiveExponentPrefix k (B + 1) × Fin (V + 1)) :=
      Fintype.card_le_of_injective e hinj
    _ = Nat.choose B k * (V + 1) := by
      rw [Fintype.card_prod, positive_exponent_prefix_card]
      · simp
      · omega

private lemma allikvere_choose_le_two_pow (B k : ℕ) :
    Nat.choose B k ≤ 2 ^ B := by
  by_cases hk : k ≤ B
  · have hterm : Nat.choose B k ≤ ∑ i ∈ Finset.range (B + 1), Nat.choose B i :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _)
        (Finset.mem_range.mpr (by omega))
    simpa [Nat.sum_range_choose] using hterm
  · rw [Nat.choose_eq_zero_of_lt (by omega)]
    exact Nat.zero_le _

theorem allikvere_bounded_prefix_last_card_le_pow
    (k B V : ℕ) :
    Fintype.card (AllikvereBoundedPrefixLast k B V) ≤
      2 ^ B * (V + 1) := by
  exact (allikvere_bounded_prefix_last_card_le_choose k B V).trans
    (Nat.mul_le_mul_right (V + 1) (allikvere_choose_le_two_pow B k))


/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under GPL-3.0-or-later as described in the file LICENSE.
Authors: Adam McKenna.
-/


set_option autoImplicit false

open Finset
open scoped BigOperators

noncomputable section

/-! Finite discrepancy for an affine arithmetic progression modulo a positive
modulus.  The finite segment is represented by its starting value and its
number of consecutive indices, so length zero is included literally. -/

def affineResidueIndices (q start step residue length : ℕ) : Finset ℕ :=
  (range length).filter (fun j => Nat.ModEq q (start + step * j) residue)

private lemma affine_modEq_reindex
    (q start step residue : ℕ) (hq : 0 < q) (hcop : step.Coprime q) :
    ∃ v : ℕ, ∀ j : ℕ,
      Nat.ModEq q (start + step * j) residue ↔ Nat.ModEq q j v := by
  letI : NeZero q := ⟨Nat.ne_of_gt hq⟩
  let u : (ZMod q)ˣ := ZMod.unitOfCoprime step hcop
  let v : ℕ := ((↑(u⁻¹) * ((residue : ZMod q) - (start : ZMod q))).val)
  refine ⟨v, ?_⟩
  intro j
  have hmod (x y : ℕ) : Nat.ModEq q x y ↔
      (x : ZMod q) = (y : ZMod q) := by
    simpa using (ZMod.natCast_eq_natCast_iff x y q).symm
  rw [hmod, hmod]
  simp only [Nat.cast_add, Nat.cast_mul, v, ZMod.natCast_zmod_val]
  constructor
  · intro h
    have h' : (step : ZMod q) * (j : ZMod q) =
        (residue : ZMod q) - (start : ZMod q) := by
      rw [← h]
      ring
    have hu : (u : ZMod q) = (step : ZMod q) := by
      exact ZMod.coe_unitOfCoprime step hcop
    rw [← hu] at h'
    calc
      (j : ZMod q) = (↑(u⁻¹) : ZMod q) * ((u : ZMod q) * (j : ZMod q)) := by
        simp
      _ = (↑(u⁻¹) : ZMod q) *
          ((residue : ZMod q) - (start : ZMod q)) := by rw [h']
  · intro h
    have hu : (u : ZMod q) = (step : ZMod q) := by
      exact ZMod.coe_unitOfCoprime step hcop
    have h' := congrArg (fun z : ZMod q => (u : ZMod q) * z) h
    calc
      (start : ZMod q) + (step : ZMod q) * (j : ZMod q) =
          (start : ZMod q) + (u : ZMod q) * (j : ZMod q) := by rw [hu]
      _ = (start : ZMod q) +
          ((residue : ZMod q) - (start : ZMod q)) := by
            rw [h']
            simp
      _ = (residue : ZMod q) := by ring

theorem affineResidueIndices_card_bounds
    (q start step residue length : ℕ) (hq : 0 < q) (hcop : step.Coprime q) :
    length / q ≤ (affineResidueIndices q start step residue length).card ∧
      (affineResidueIndices q start step residue length).card ≤ length / q + 1 := by
  obtain ⟨v, hv⟩ := affine_modEq_reindex q start step residue hq hcop
  have hfilter : affineResidueIndices q start step residue length =
      (range length).filter (fun j => Nat.ModEq q j v) := by
    ext j
    simp [affineResidueIndices, hv]
  rw [hfilter]
  have hcount := Nat.count_modEq_card (b := length) (r := q) hq v
  have hcount' :
      ((range length).filter (fun j => Nat.ModEq q j v)).card =
        length / q + if v % q < length % q then 1 else 0 := by
    rw [← Nat.count_eq_card_filter_range]
    exact hcount
  rw [hcount']
  split_ifs <;> omega

theorem affineResidueIndices_card_discrepancy
    (q start step residue length : ℕ) (hq : 0 < q) (hcop : step.Coprime q) :
    |((affineResidueIndices q start step residue length).card : ℝ) -
        (length : ℝ) / q| ≤ 1 := by
  have hbounds := affineResidueIndices_card_bounds q start step residue length hq hcop
  have hqR : (0 : ℝ) < (q : ℝ) := by positivity
  have hdecomp : (length : ℝ) =
    ((length / q : ℕ) : ℝ) * (q : ℝ) + ((length % q : ℕ) : ℝ) := by
    have hdecompNat : length = length / q * q + length % q := by
      simpa [Nat.mul_comm] using (Nat.div_add_mod length q).symm
    exact_mod_cast hdecompNat
  have hrem : ((length % q : ℕ) : ℝ) < (q : ℝ) := by
    exact_mod_cast Nat.mod_lt length hq
  have hfloor : ((length / q : ℕ) : ℝ) ≤ (length : ℝ) / q := by
    apply (le_div_iff₀ hqR).2
    nlinarith [hdecomp, Nat.zero_le (length % q)]
  have hfrac : (length : ℝ) / q < ((length / q : ℕ) : ℝ) + 1 := by
    apply (div_lt_iff₀ hqR).2
    nlinarith [hdecomp, hrem]
  have hcardlo : ((length / q : ℕ) : ℝ) ≤
      ((affineResidueIndices q start step residue length).card : ℝ) := by
    exact_mod_cast hbounds.1
  have hcardhi : ((affineResidueIndices q start step residue length).card : ℝ) ≤
      ((length / q : ℕ) : ℝ) + 1 := by
    exact_mod_cast hbounds.2
  have hlo : (length : ℝ) / q -
      ((affineResidueIndices q start step residue length).card : ℝ) ≤ 1 := by
    nlinarith [hfrac, hcardlo]
  have hhi : ((affineResidueIndices q start step residue length).card : ℝ) -
      (length : ℝ) / q ≤ 1 := by
    nlinarith [hfloor, hcardhi]
  rw [abs_le]
  exact ⟨by linarith [hlo], hhi⟩

/-- The original orientation: a step `3^k` progression sampled modulo `2^(B+1)`. -/
theorem syracuse_three_pow_two_pow_affine_discrepancy
    (B k start residue length : ℕ) :
    |((affineResidueIndices (2 ^ (B + 1)) start (3 ^ k) residue length).card : ℝ) -
        (length : ℝ) / ((2 ^ (B + 1) : ℕ) : ℝ)| ≤ 1 := by
  have hq : 0 < 2 ^ (B + 1) := by positivity
  have hcop : Nat.Coprime (3 ^ k) (2 ^ (B + 1)) := by
    exact ((by decide : Nat.Coprime 3 2).pow_left k).pow_right (B + 1)
  exact affineResidueIndices_card_discrepancy
    (2 ^ (B + 1)) start (3 ^ k) residue length hq hcop

/-- A `2^(B+1)` progression has discrepancy at most one modulo `3^k`. -/
theorem syracuse_two_pow_three_pow_affine_discrepancy
    (B k start residue length : ℕ) :
    |((affineResidueIndices (3 ^ k) start (2 ^ (B + 1)) residue length).card : ℝ) -
        (length : ℝ) / ((3 ^ k : ℕ) : ℝ)| ≤ 1 := by
  have hq : 0 < 3 ^ k := by positivity
  have hcop : Nat.Coprime (2 ^ (B + 1)) (3 ^ k) := by
    exact ((by decide : Nat.Coprime 2 3).pow_left (B + 1)).pow_right k
  exact affineResidueIndices_card_discrepancy
    (3 ^ k) start (2 ^ (B + 1)) residue length hq hcop

/-- Values of the finite affine progression `start + step * j`, `j < length`. -/
def affineResidueValues (start step length : ℕ) : Finset ℕ :=
  (range length).image (fun j => start + step * j)

/-- A positive-step affine progression has exactly `length` distinct values. -/
theorem affineResidueValues_card
    (start step length : ℕ) (hstep : 0 < step) :
    (affineResidueValues start step length).card = length := by
  unfold affineResidueValues
  have hinj : Function.Injective (fun j : ℕ => start + step * j) := by
    intro i j hij
    apply Nat.eq_of_mul_eq_mul_left hstep
    exact Nat.add_left_cancel hij
  rw [Finset.card_image_of_injective _ hinj, card_range]

/-- Membership in `affineResidueValues` exposes its consecutive index. -/
theorem mem_affineResidueValues_iff
    (start step length x : ℕ) :
    x ∈ affineResidueValues start step length ↔
      ∃ j, j < length ∧ x = start + step * j := by
  constructor
  · simp only [affineResidueValues, mem_image, mem_range]
    rintro ⟨j, hj, rfl⟩
    exact ⟨j, hj, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    exact mem_image.mpr ⟨j, mem_range.mpr hj, rfl⟩

/-- Members of `[lo, hi]` whose remainder modulo `step` is `residue`. -/
def intervalResidueValues (lo hi step residue : ℕ) : Finset ℕ :=
  (Icc lo hi).filter (fun M => M % step = residue)

/-- Every interval residue class is a finite affine progression, also when empty. -/
theorem intervalResidueValues_eq_affineResidueValues
    (lo hi step residue : ℕ) (hstep : 0 < step) (hresidue : residue < step) :
    ∃ start length,
      intervalResidueValues lo hi step residue =
        affineResidueValues start step length := by
  let first : ℕ := if lo ≤ residue then 0 else
    (lo - residue) ⌈/⌉ step
  let last : ℕ := if residue ≤ hi then (hi - residue) / step else 0
  let length : ℕ := if residue ≤ hi ∧ first ≤ last then last - first + 1 else 0
  let start : ℕ := residue + step * first
  refine ⟨start, length, ?_⟩
  by_cases hlo : lo ≤ residue
  · by_cases hhi : residue ≤ hi
    · have hfirst : first = 0 := by simp [first, hlo]
      have hlast : last = (hi - residue) / step := by simp [last, hhi]
      simp [first, last, length, start, hhi, hfirst, hlast]
      ext x
      simp only [intervalResidueValues, mem_filter, mem_Icc,
        affineResidueValues, mem_image, mem_range]
      constructor
      · rintro ⟨⟨hlox, hxhi⟩, hxmod⟩
        have hxrepr : x = residue + step * (x / step) := by
          calc
            x = x % step + step * (x / step) := (Nat.mod_add_div x step).symm
            _ = residue + step * (x / step) := by rw [hxmod]
        refine ⟨x / step, ?_, hxrepr.symm⟩
        rw [hxrepr] at hxhi
        have hjhi : x / step ≤ (hi - residue) / step := by
          apply (Nat.le_div_iff_mul_le hstep).2
          exact Nat.le_sub_of_add_le' (by simpa [Nat.mul_comm] using hxhi)
        exact Nat.lt_succ_of_le hjhi
      · rintro ⟨j, hj, rfl⟩
        have hjhi : step * j ≤ hi - residue := by
          simpa [Nat.mul_comm] using
            (Nat.le_div_iff_mul_le hstep).1 (Nat.le_of_lt_succ hj)
        have hxhi : residue + step * j ≤ hi := by
          exact Nat.add_le_of_le_sub' hhi hjhi
        refine ⟨⟨by omega, hxhi⟩, ?_⟩
        simp [Nat.add_mod, Nat.mod_eq_of_lt hresidue]
    · simp [first, last, length, start, hlo, hhi]
      ext x
      simp only [intervalResidueValues, mem_filter, mem_Icc,
        affineResidueValues, mem_image, mem_range]
      constructor
      · rintro ⟨⟨hlox, hxhi⟩, hxmod⟩
        have hxrepr : x = residue + step * (x / step) := by
          calc
            x = x % step + step * (x / step) := (Nat.mod_add_div x step).symm
            _ = residue + step * (x / step) := by rw [hxmod]
        rw [hxrepr] at hlox hxhi
        omega
      · rintro ⟨j, hj, rfl⟩
        omega
  · by_cases hhi : residue ≤ hi
    · have hfirst : first = (lo - residue) ⌈/⌉ step := by simp [first, hlo]
      have hlast : last = (hi - residue) / step := by simp [last, hhi]
      by_cases hbounds : (lo - residue) ⌈/⌉ step ≤ (hi - residue) / step
      · have hlength : length = (hi - residue) / step -
            (lo - residue) ⌈/⌉ step + 1 := by
          simp [length, first, last, hhi, hbounds, hfirst, hlast]
        simp [first, length, start, hfirst, hlength]
        ext x
        simp only [intervalResidueValues, mem_filter, mem_Icc,
          affineResidueValues, mem_image, mem_range]
        constructor
        · rintro ⟨⟨hlox, hxhi⟩, hxmod⟩
          have hxrepr : x = residue + step * (x / step) := by
            calc
              x = x % step + step * (x / step) := (Nat.mod_add_div x step).symm
              _ = residue + step * (x / step) := by rw [hxmod]
          rw [hxrepr] at hlox hxhi
          refine ⟨x / step - ((lo - residue) ⌈/⌉ step), ?_, ?_⟩
          · have hlow : (lo - residue) ≤ step * (x / step) := by
              rw [Nat.sub_le_iff_le_add]
              simpa [Nat.mul_comm, Nat.add_comm] using hlox
            have hjlow : (lo - residue) ⌈/⌉ step ≤ x / step :=
              (ceilDiv_le_iff_le_mul hstep).2 hlow
            have hjhi : x / step ≤ (hi - residue) / step := by
              apply (Nat.le_div_iff_mul_le hstep).2
              exact Nat.le_sub_of_add_le' (by simpa [Nat.mul_comm] using hxhi)
            omega
          · have hjlow : (lo - residue) ⌈/⌉ step ≤ x / step := by
              exact (ceilDiv_le_iff_le_mul hstep).2 (by
                rw [Nat.sub_le_iff_le_add]
                simpa [Nat.mul_comm, Nat.add_comm] using hlox)
            calc
              residue + step * ((lo - residue) ⌈/⌉ step) +
                    step * (x / step - (lo - residue) ⌈/⌉ step) =
                  residue + step * ((lo - residue) ⌈/⌉ step +
                    (x / step - (lo - residue) ⌈/⌉ step)) := by
                      simp only [Nat.mul_add, add_assoc]
              _ = residue + step * (x / step) := by
                rw [Nat.add_sub_of_le hjlow]
              _ = x := hxrepr.symm
        · rintro ⟨j, hj, rfl⟩
          have hjhi : (lo - residue) ⌈/⌉ step + j ≤ (hi - residue) / step := by
            omega
          have hlowmul : lo - residue ≤
              step * ((lo - residue) ⌈/⌉ step + j) := by
            have hceil : lo - residue ≤
                step * ((lo - residue) ⌈/⌉ step) :=
              (ceilDiv_le_iff_le_mul hstep).1 le_rfl
            calc
              lo - residue ≤ step * ((lo - residue) ⌈/⌉ step) := hceil
              _ ≤ step * ((lo - residue) ⌈/⌉ step) + step * j := by omega
              _ = step * ((lo - residue) ⌈/⌉ step + j) := by rw [Nat.mul_add]
          have hxlo : lo ≤ residue +
              step * ((lo - residue) ⌈/⌉ step + j) := by
            simpa [Nat.add_comm, Nat.mul_add, add_assoc] using
              (Nat.sub_le_iff_le_add').1 hlowmul
          have hxhi : residue +
              step * ((lo - residue) ⌈/⌉ step + j) ≤ hi := by
            have hmul : step * ((lo - residue) ⌈/⌉ step + j) ≤ hi - residue :=
              by simpa [Nat.mul_comm] using
                (Nat.le_div_iff_mul_le hstep).1 hjhi
            exact Nat.add_le_of_le_sub' hhi hmul
          have hxlo' : lo ≤ residue +
              step * ((lo - residue) ⌈/⌉ step) + step * j := by
            simpa [Nat.mul_add, add_assoc, add_comm, add_left_comm] using hxlo
          have hxhi' : residue +
              step * ((lo - residue) ⌈/⌉ step) + step * j ≤ hi := by
            simpa [Nat.mul_add, add_assoc, add_comm, add_left_comm] using hxhi
          refine ⟨⟨hxlo', hxhi'⟩, ?_⟩
          simp [Nat.add_mod, Nat.mod_eq_of_lt hresidue]
      · simp [first, last, length, start, hlo, hhi, hbounds]
        ext x
        simp only [intervalResidueValues, mem_filter, mem_Icc,
          affineResidueValues, mem_image, mem_range]
        constructor
        · rintro ⟨⟨hlox, hxhi⟩, hxmod⟩
          have hxrepr : x = residue + step * (x / step) := by
            calc
              x = x % step + step * (x / step) := (Nat.mod_add_div x step).symm
              _ = residue + step * (x / step) := by rw [hxmod]
          rw [hxrepr] at hlox hxhi
          have hjlow : (lo - residue) ⌈/⌉ step ≤ x / step := by
            apply (ceilDiv_le_iff_le_mul hstep).2
            rw [Nat.sub_le_iff_le_add]
            simpa [Nat.mul_comm, Nat.add_comm] using hlox
          have hjhi : x / step ≤ (hi - residue) / step := by
            apply (Nat.le_div_iff_mul_le hstep).2
            exact Nat.le_sub_of_add_le' (by simpa [Nat.mul_comm] using hxhi)
          omega
        · rintro ⟨j, hj, rfl⟩
          omega
    · simp [first, last, length, start, hlo, hhi]
      ext x
      simp only [intervalResidueValues, mem_filter, mem_Icc,
        affineResidueValues, mem_image, mem_range]
      constructor
      · rintro ⟨⟨hlox, hxhi⟩, hxmod⟩
        have hxrepr : x = residue + step * (x / step) := by
          calc
            x = x % step + step * (x / step) := (Nat.mod_add_div x step).symm
            _ = residue + step * (x / step) := by rw [hxmod]
        rw [hxrepr] at hlox hxhi
        omega
      · rintro ⟨j, hj, rfl⟩
        omega

/-- Filtering affine progression values by a target modulus equals filtering indices. -/
theorem affineResidueValues_filter_card
    (q start step residue length : ℕ) (hstep : 0 < step) :
    ((affineResidueValues start step length).filter
      (fun M => Nat.ModEq q M residue)).card =
      (affineResidueIndices q start step residue length).card := by
  have hinj : Function.Injective (fun j : ℕ => start + step * j) := by
    intro i j hij
    apply Nat.eq_of_mul_eq_mul_left hstep
    exact Nat.add_left_cancel hij
  have heq : (affineResidueValues start step length).filter
      (fun M => Nat.ModEq q M residue) =
      (affineResidueIndices q start step residue length).image
        (fun j => start + step * j) := by
    ext x
    constructor
    · intro hx
      rcases mem_filter.mp hx with ⟨hxv, hxq⟩
      change x ∈ (range length).image (fun j => start + step * j) at hxv
      rcases mem_image.mp hxv with ⟨j, hj, rfl⟩
      exact mem_image.mpr ⟨j, mem_filter.mpr ⟨hj, hxq⟩, rfl⟩
    · intro hx
      rcases mem_image.mp hx with ⟨j, hj, rfl⟩
      rcases mem_filter.mp hj with ⟨hjrange, hjq⟩
      refine mem_filter.mpr ⟨?_, hjq⟩
      exact mem_image.mpr ⟨j, hjrange, rfl⟩
  rw [heq, Finset.card_image_of_injective _ hinj]

/-- A target modulus sees an interval residue class with discrepancy at most one. -/
theorem intervalResidueValues_card_discrepancy
    (lo hi step prefixResidue q targetResidue : ℕ)
    (hstep : 0 < step) (hresidue : prefixResidue < step)
    (hq : 0 < q) (hcop : step.Coprime q) :
    |(((intervalResidueValues lo hi step prefixResidue).filter
        (fun M => Nat.ModEq q M targetResidue)).card : ℝ) -
        ((intervalResidueValues lo hi step prefixResidue).card : ℝ) / q| ≤ 1 := by
  obtain ⟨start, length, hset⟩ :=
    intervalResidueValues_eq_affineResidueValues
      lo hi step prefixResidue hstep hresidue
  rw [hset, affineResidueValues_filter_card q start step targetResidue length hstep,
    affineResidueValues_card start step length hstep]
  exact affineResidueIndices_card_discrepancy
    q start step targetResidue length hq hcop


end


/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under GPL-3.0-or-later as described in the file LICENSE.
Authors: Adam McKenna.
-/



set_option autoImplicit false

open scoped BigOperators

/-!
  Orbit bounds for the Allikvere Lemma 6.3 prefix-count consumer.

  This module deliberately does not define the source set `E'`, Tao's range, or
  the admissible-prefix count.  It supplies only the affine-error and terminal
  valuation estimates used by that consumer.
-/

noncomputable section

/-- The real affine error attached to a finite valuation list. -/
def syracuseAffineError (as : List ℕ) : ℝ :=
  (syracuseAffineConstant as : ℝ) / (2 : ℝ) ^ as.sum

private lemma syracuseAffineError_term_le (a : ℕ) (as : List ℕ) :
    (3 : ℝ) ^ as.length / (2 : ℝ) ^ (a + as.sum) ≤ (3 : ℝ) ^ as.length := by
  have hden : (0 : ℝ) < (2 : ℝ) ^ (a + as.sum) := by positivity
  have hone : (1 : ℝ) ≤ (2 : ℝ) ^ (a + as.sum) := by
    exact one_le_pow₀ (by norm_num)
  apply (div_le_iff₀ hden).2
  nlinarith [pow_nonneg (show (0 : ℝ) ≤ 3 by norm_num) as.length]

/-- The affine error is bounded by the geometric sum's largest scale. -/
theorem syracuseAffineError_le_three_pow (as : List ℕ) :
    syracuseAffineError as ≤ (3 : ℝ) ^ as.length := by
  induction as with
  | nil => simp [syracuseAffineError, syracuseAffineConstant]
  | cons a as ih =>
      rw [syracuseAffineError, syracuseAffineConstant, List.sum_cons, pow_add]
      push_cast
      have hden : (0 : ℝ) < (2 : ℝ) ^ as.sum := by positivity
      have hrewrite :
          ((3 : ℝ) ^ as.length + (2 : ℝ) ^ a * syracuseAffineConstant as) /
              ((2 : ℝ) ^ a * (2 : ℝ) ^ as.sum) =
            (3 : ℝ) ^ as.length / (2 : ℝ) ^ (a + as.sum) +
              syracuseAffineError as := by
        unfold syracuseAffineError
        field_simp [ne_of_gt hden]
        ring
      rw [hrewrite]
      have hterm := syracuseAffineError_term_le a as
      have hsum :
          (3 : ℝ) ^ as.length / (2 : ℝ) ^ (a + as.sum) + syracuseAffineError as ≤
            2 * (3 : ℝ) ^ as.length := by
        simpa [two_mul] using add_le_add hterm ih
      calc
        (3 : ℝ) ^ as.length / (2 : ℝ) ^ (a + as.sum) + syracuseAffineError as ≤
            2 * (3 : ℝ) ^ as.length := hsum
        _ ≤ (3 : ℝ) ^ (as.length + 1) := by
          rw [pow_succ]
          nlinarith [pow_nonneg (show (0 : ℝ) ≤ 3 by norm_num) as.length]

/-- The affine numerator after appending one valuation. -/
private lemma syracuseAffineNumerator_append_singleton (as : List ℕ) (a M : ℕ) :
    syracuseAffineNumerator (as ++ [a]) M =
      3 * syracuseAffineNumerator as M + 2 ^ as.sum := by
  induction as generalizing M with
  | nil => simp [syracuseAffineNumerator, syracuseAffineConstant]
  | cons b as ih =>
      rw [List.cons_append, syracuseAffineNumerator_cons b (as ++ [a]) M,
        syracuseAffineNumerator_cons b as M, ih 0]
      simp only [List.sum_cons, List.length_append, List.length_singleton, pow_add]
      ring

def syracuseOrbitValuationList (M j : ℕ) : List ℕ :=
  List.ofFn (fun i : Fin j => syracuseExponent M i)

def syracuseOrbitAffineError (M j : ℕ) : ℝ :=
  syracuseAffineError (syracuseOrbitValuationList M j)

private lemma syracuseOrbitValuationList_succ (M j : ℕ) :
    syracuseOrbitValuationList M (j + 1) =
      syracuseOrbitValuationList M j ++ [syracuseExponent M j] := by
  unfold syracuseOrbitValuationList
  rw [List.ofFn_succ']
  have hleft :
      List.ofFn (fun i : Fin j => syracuseExponent M (Fin.castSucc i)) =
        List.ofFn (fun i : Fin j => syracuseExponent M i) := by
    congr 1
  rw [hleft]
  simp [List.concat_eq_append]

private lemma syracuseOrbitValuationList_sum (M j : ℕ) :
    (syracuseOrbitValuationList M j).sum = ∑ i : Fin j, syracuseExponent M i := by
  induction j with
  | zero => simp [syracuseOrbitValuationList]
  | succ j ih =>
      change (List.ofFn (fun i : Fin (j + 1) => syracuseExponent M i)).sum = _
      rw [List.ofFn_succ', List.sum_concat]
      have hleft :
          List.ofFn (fun i : Fin j => syracuseExponent M (Fin.castSucc i)) =
            List.ofFn (fun i : Fin j => syracuseExponent M i) := by
        congr 1
      have ih' :
          (List.ofFn (fun i : Fin j => syracuseExponent M i)).sum =
            ∑ i : Fin j, syracuseExponent M i := by
        simpa [syracuseOrbitValuationList] using ih
      rw [hleft, ih', Fin.sum_univ_castSucc]
      rfl

/-- The actual Syracuse iterate satisfies the affine numerator identity. -/
theorem syracuse_iterate_affine_numerator (M j : ℕ) (hM : 0 < M) (hodd : Odd M) :
    2 ^ (∑ i : Fin j, syracuseExponent M i) * (syracuseStep^[j]) M =
      syracuseAffineNumerator (syracuseOrbitValuationList M j) M := by
  induction j with
  | zero => simp [syracuseOrbitValuationList, syracuseAffineNumerator, syracuseAffineConstant]
  | succ j ih =>
      simp only [Function.iterate_succ_apply']
      have hposodd := syracuse_iterate_pos_odd M hM hodd j
      have hchain := syracuse_exponent_chain M j
      rw [Function.iterate_succ_apply'] at hchain
      have hsum :
          (∑ i : Fin (j + 1), syracuseExponent M i) =
            (∑ i : Fin j, syracuseExponent M i) + syracuseExponent M j := by
        rw [Fin.sum_univ_castSucc]
        rfl
      rw [hsum, pow_add]
      rw [syracuseOrbitValuationList_succ, syracuseAffineNumerator_append_singleton]
      have hlist_sum : (syracuseOrbitValuationList M j).sum =
          ∑ i : Fin j, syracuseExponent M i := by
        exact syracuseOrbitValuationList_sum M j
      calc
        2 ^ (∑ i : Fin j, syracuseExponent M i) *
              2 ^ syracuseExponent M j * syracuseStep ((syracuseStep^[j]) M) =
            2 ^ (∑ i : Fin j, syracuseExponent M i) *
              (2 ^ syracuseExponent M j * syracuseStep ((syracuseStep^[j]) M)) := by ring
        _ = 2 ^ (∑ i : Fin j, syracuseExponent M i) *
              (3 * (syracuseStep^[j]) M + 1) := by rw [hchain]
        _ = 3 * (2 ^ (∑ i : Fin j, syracuseExponent M i) *
              (syracuseStep^[j]) M) +
              2 ^ (∑ i : Fin j, syracuseExponent M i) := by ring
        _ = 3 * syracuseAffineNumerator (syracuseOrbitValuationList M j) M +
              2 ^ (syracuseOrbitValuationList M j).sum := by rw [ih, hlist_sum]

/-- The paper's affine error is the error in the actual orbit identity. -/
theorem syracuse_iterate_affine_identity (M j : ℕ) (hM : 0 < M) (hodd : Odd M) :
    ((syracuseStep^[j]) M : ℝ) =
      (3 : ℝ) ^ j /
          (2 : ℝ) ^ (∑ i : Fin j, syracuseExponent M i) * M +
        syracuseOrbitAffineError M j := by
  have hnum := syracuse_iterate_affine_numerator M j hM hodd
  have hden : (0 : ℝ) < (2 : ℝ) ^ (∑ i : Fin j, syracuseExponent M i) := by positivity
  have hnumR :
      (2 : ℝ) ^ (∑ i : Fin j, syracuseExponent M i) *
          (syracuseStep^[j]) M =
        (3 : ℝ) ^ j * M +
          (syracuseAffineConstant (syracuseOrbitValuationList M j) : ℝ) := by
    simpa [syracuseAffineNumerator, syracuseOrbitValuationList] using
      (congrArg (fun z : ℕ => (z : ℝ)) hnum)
  unfold syracuseOrbitAffineError syracuseAffineError
  have hlist_sum : (syracuseOrbitValuationList M j).sum =
      ∑ i : Fin j, syracuseExponent M i := by
    exact syracuseOrbitValuationList_sum M j
  rw [hlist_sum]
  field_simp [ne_of_gt hden]
  nlinarith [hnumR]

/-- The same affine-error bound in the finite-prefix representation. -/
def syracuseAffineErrorFin (t : ℕ) (a : Fin t → ℕ) : ℝ :=
  syracuseAffineError (List.ofFn a)

theorem syracuseAffineErrorFin_le_three_pow (t : ℕ) (a : Fin t → ℕ) :
    syracuseAffineErrorFin t a ≤ (3 : ℝ) ^ t := by
  simpa [syracuseAffineErrorFin] using syracuseAffineError_le_three_pow (List.ofFn a)

theorem syracuse_step_le_two_mul {n : ℕ} (hn : 0 < n) (hodd : Odd n) :
    syracuseStep n ≤ 2 * n := by
  let v := (3 * n + 1).factorization 2
  have hv : 0 < v := by
    dsimp [v]
    exact syracuse_step_factorization_pos hn hodd
  have hpow : 2 ≤ 2 ^ v := by
    simpa using Nat.pow_le_pow_right (by omega : 1 ≤ (2 : ℕ)) hv
  have hmul : 2 * syracuseStep n ≤ 2 ^ v * syracuseStep n :=
    Nat.mul_le_mul_right _ hpow
  have hchain : 2 ^ v * syracuseStep n = 3 * n + 1 := by
    dsimp [v]
    exact syracuse_step_factorization_mul (n := n)
  rw [hchain] at hmul
  have hlinear : 3 * n + 1 ≤ 4 * n := by omega
  omega

/-- Every positive odd Syracuse orbit iterate is bounded by `3^j * M`. -/
theorem syracuse_iterate_le_three_pow_mul (M j : ℕ) (hM : 0 < M) (hodd : Odd M) :
    (syracuseStep^[j]) M ≤ 3 ^ j * M := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [Function.iterate_succ_apply']
      obtain ⟨hpos, hoddj⟩ := syracuse_iterate_pos_odd M hM hodd j
      have hstep2 := syracuse_step_le_two_mul hpos hoddj
      have hstep3 : syracuseStep ((syracuseStep^[j]) M) ≤ 3 * (syracuseStep^[j]) M := by
        omega
      calc
        syracuseStep ((syracuseStep^[j]) M) ≤ 3 * (syracuseStep^[j]) M := hstep3
        _ ≤ 3 * (3 ^ j * M) := Nat.mul_le_mul_left _ ih
        _ = 3 ^ (j + 1) * M := by rw [pow_succ]; ring

/-- The actual next valuation power is bounded by the orbit upper envelope. -/
theorem syracuse_next_valuation_pow_le_orbit_upper (M j : ℕ) (hM : 0 < M) (hodd : Odd M) :
    2 ^ syracuseExponent M j ≤ 3 ^ (j + 2) * M := by
  obtain ⟨hpos, hoddj⟩ := syracuse_iterate_pos_odd M hM hodd j
  have hstep : 0 < syracuseStep ((syracuseStep^[j]) M) := syracuse_step_pos hpos
  have hchain := syracuse_exponent_chain M j
  rw [Function.iterate_succ_apply'] at hchain
  have hleft : 2 ^ syracuseExponent M j ≤
      2 ^ syracuseExponent M j * syracuseStep ((syracuseStep^[j]) M) :=
    Nat.le_mul_of_pos_right _ hstep
  have hupper : 3 * (syracuseStep^[j]) M + 1 ≤ 3 ^ (j + 2) * M := by
    have hiter := syracuse_iterate_le_three_pow_mul M j hM hodd
    have hA : 0 < 3 ^ (j + 1) * M := by positivity
    calc
      3 * (syracuseStep^[j]) M + 1 ≤ 3 * (3 ^ j * M) + 1 := by omega
      _ = 3 ^ (j + 1) * M + 1 := by rw [pow_succ]; ring
      _ ≤ 3 * (3 ^ (j + 1) * M) := by omega
      _ = 3 ^ (j + 2) * M := by rw [pow_succ]; ring
  rw [hchain] at hleft
  exact hleft.trans hupper

/-- The actual next valuation is bounded by the real base-2 logarithm of that envelope. -/
theorem syracuse_next_valuation_le_logb_orbit_upper (M j : ℕ) (hM : 0 < M) (hodd : Odd M) :
    (syracuseExponent M j : ℝ) ≤
      Real.logb 2 ((3 ^ (j + 2) * M : ℕ) : ℝ) := by
  have hpow := syracuse_next_valuation_pow_le_orbit_upper M j hM hodd
  have hupper : 0 < ((3 ^ (j + 2) * M : ℕ) : ℝ) := by positivity
  apply (Real.le_logb_iff_rpow_le (b := (2 : ℝ)) (x := (syracuseExponent M j : ℝ))
    (y := ((3 ^ (j + 2) * M : ℕ) : ℝ)) (by norm_num) hupper).2
  have hpow' : ((2 ^ syracuseExponent M j : ℕ) : ℝ) ≤
      ((3 ^ (j + 2) * M : ℕ) : ℝ) := by
    exact_mod_cast hpow
  simpa [Real.rpow_natCast] using hpow'


private theorem syracuseAffineError_mul_pow_eq_constant (as : List ℕ) :
    (2 : ℝ) ^ as.sum * syracuseAffineError as =
      (syracuseAffineConstant as : ℝ) := by
  unfold syracuseAffineError
  have hpow : (2 : ℝ) ^ as.sum ≠ 0 := by positivity
  field_simp [hpow]

theorem syracuse_iterate_mul_pow_eq_affine_error (M t : ℕ)
    (hM : 0 < M) (hodd : Odd M) :
    (2 : ℝ) ^ (∑ i : Fin t, syracuseExponent M i) *
        ((syracuseStep^[t]) M : ℝ) =
      (3 : ℝ) ^ t * M +
        (2 : ℝ) ^ (∑ i : Fin t, syracuseExponent M i) *
          syracuseAffineErrorFin t (fun i : Fin t => syracuseExponent M i) := by
  have haff := syracuse_iterate_affine_numerator M t hM hodd
  have hreal := congrArg (fun n : ℕ => (n : ℝ)) haff
  rw [syracuseAffineErrorFin]
  have herr := syracuseAffineError_mul_pow_eq_constant (List.ofFn
    (fun i : Fin t => syracuseExponent M i))
  have herr' :
      (2 : ℝ) ^ (∑ i : Fin t, syracuseExponent M i) *
          syracuseAffineError (List.ofFn
            (fun i : Fin t => syracuseExponent M i)) =
        (syracuseAffineConstant
          (List.ofFn (fun i : Fin t => syracuseExponent M i)) : ℝ) := by
    simpa [List.sum_ofFn] using herr
  have hreal' :
      (2 : ℝ) ^ (∑ i : Fin t, syracuseExponent M i) *
          ((syracuseStep^[t]) M : ℝ) =
        (3 : ℝ) ^ t * M +
          (syracuseAffineConstant
            (List.ofFn (fun i : Fin t => syracuseExponent M i)) : ℝ) := by
    simpa [syracuseOrbitValuationList, syracuseAffineNumerator,
      List.length_ofFn, Nat.cast_mul,
      Nat.cast_pow] using hreal
  calc
    (2 : ℝ) ^ (∑ i : Fin t, syracuseExponent M i) *
          ((syracuseStep^[t]) M : ℝ) =
        (3 : ℝ) ^ t * M +
          (syracuseAffineConstant
            (List.ofFn (fun i : Fin t => syracuseExponent M i)) : ℝ) := hreal'
    _ = (3 : ℝ) ^ t * M +
          (2 : ℝ) ^ (∑ i : Fin t, syracuseExponent M i) *
            syracuseAffineError (List.ofFn
              (fun i : Fin t => syracuseExponent M i)) := by
      rw [herr']

theorem allikvereM0_eq_floor (x : ℝ) :
    allikvereM0 x = Nat.floor (Real.log x / 100000) := rfl

theorem allikvereEPrime_mem_pos_odd {x : ℝ} {M : ℕ}
    (hM : M ∈ allikvereEPrime x) : 0 < M ∧ Odd M := by
  exact ⟨hM.2.1, hM.1⟩

theorem allikvereEPrime_pass_pos_le {x : ℝ} {M : ℕ}
    (hM : M ∈ allikvereEPrime x) :
    1 ≤ (syracuseStep^[allikvereM0 x]) M ∧
      ((syracuseStep^[allikvereM0 x]) M : ℝ) ≤ x := by
  have hpass := hM.2.2.2
  exact hpass.2

theorem allikvere_previous_power_upper_bound {x : ℝ} {M : ℕ}
    (hM : M ∈ allikvereEPrime x)
    (hm : 0 < allikvereM0 x)
    (hthree : (3 : ℝ) ^ allikvereM0 x ≤ x / 2) :
    (2 : ℝ) ^ (∑ i : Fin (allikvereM0 x - 1), syracuseExponent M i) *
        (x / 2) <
      (3 : ℝ) ^ (allikvereM0 x - 1) * M := by
  have hposodd := allikvereEPrime_mem_pos_odd hM
  let m := allikvereM0 x
  have hlt : m - 1 < m := Nat.sub_lt hm (by omega)
  have hpass := hM.2.2.2.1 (m - 1) hlt
  have hident := syracuse_iterate_mul_pow_eq_affine_error M (m - 1)
    hposodd.1 hposodd.2
  have herr := syracuseAffineErrorFin_le_three_pow (m - 1)
    (fun i : Fin (m - 1) => syracuseExponent M i)
  have hpowerr :
      (2 : ℝ) ^ (∑ i : Fin (m - 1), syracuseExponent M i) *
          syracuseAffineErrorFin (m - 1)
            (fun i : Fin (m - 1) => syracuseExponent M i) ≤
        (2 : ℝ) ^ (∑ i : Fin (m - 1), syracuseExponent M i) * (x / 2) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    calc
      syracuseAffineErrorFin (m - 1)
          (fun i : Fin (m - 1) => syracuseExponent M i) ≤
          (3 : ℝ) ^ (m - 1) := herr
      _ ≤ (3 : ℝ) ^ m := by
        gcongr <;> norm_num
      _ ≤ x / 2 := hthree
  have hleft :
      (2 : ℝ) ^ (∑ i : Fin (m - 1), syracuseExponent M i) * x <
        (3 : ℝ) ^ (m - 1) * M +
          (2 : ℝ) ^ (∑ i : Fin (m - 1), syracuseExponent M i) *
            syracuseAffineErrorFin (m - 1)
              (fun i : Fin (m - 1) => syracuseExponent M i) := by
    have hmul := mul_lt_mul_of_pos_left hpass
      (by positivity : 0 <
        (2 : ℝ) ^ (∑ i : Fin (m - 1), syracuseExponent M i))
    rw [hident] at hmul
    simpa [Nat.cast_mul, Nat.cast_pow] using hmul
  dsimp [m] at hpowerr hleft ⊢
  nlinarith

theorem allikvereEPrime_prefix_residue {x : ℝ}
    (a : Fin (allikvereM0 x) → ℕ) (ha : ∀ i, 0 < a i) :
    ∃ r : Fin (2 ^ ((∑ i, a i) + 1)),
      Odd r.val ∧
      ∀ M : ℕ, M ∈ allikvereEPrimePrefix x a ↔
        M ∈ allikvereEPrime x ∧
          M % 2 ^ ((∑ i, a i) + 1) = r.val := by
  obtain ⟨r, hr, hres⟩ := syracuse_exact_prefix_residue _ a ha
  refine ⟨r, hr, ?_⟩
  intro M
  constructor
  · intro h
    exact ⟨h.1, (hres M h.1.2.1 h.1.1).mp h.2⟩
  · rintro ⟨hM, hmod⟩
    refine ⟨hM, (hres M hM.2.1 hM.1).mpr hmod⟩

private theorem syracuseStep_le_two_mul {n : ℕ}
    (hn : 0 < n) (hodd : Odd n) : syracuseStep n ≤ 2 * n := by
  have he : 0 < (3 * n + 1).factorization 2 :=
    syracuse_step_factorization_pos hn hodd
  have hpow : 2 ≤ 2 ^ ((3 * n + 1).factorization 2) := by
    rw [show 2 = 2 ^ 1 by norm_num]
    exact Nat.pow_le_pow_right (by decide) he
  have hrec := syracuse_step_factorization_mul (n := n)
  have hle : 2 * syracuseStep n ≤ 3 * n + 1 := by
    calc
      2 * syracuseStep n ≤
          2 ^ ((3 * n + 1).factorization 2) * syracuseStep n := by
            exact Nat.mul_le_mul_right _ hpow
      _ = 3 * n + 1 := hrec
  omega

private theorem syracuse_iterate_le_pow_two {n t : ℕ}
    (hn : 0 < n) (hodd : Odd n) :
    (syracuseStep^[t]) n ≤ 2 ^ t * n := by
  induction t generalizing n with
  | zero => simp
  | succ t ih =>
      rw [Function.iterate_succ_apply']
      have htail := ih (n := n) hn hodd
      have hposodd := syracuse_iterate_pos_odd n hn hodd t
      have hstep := syracuseStep_le_two_mul hposodd.1 hposodd.2
      calc
        syracuseStep ((syracuseStep^[t]) n) ≤
            2 * (syracuseStep^[t]) n := hstep
        _ ≤ 2 * (2 ^ t * n) := Nat.mul_le_mul_left _ htail
        _ = 2 ^ (t + 1) * n := by
          rw [pow_succ]
          ring

theorem allikvere_terminal_valuation_bound {x : ℝ} {M : ℕ}
    (hM : M ∈ allikvereEPrime x)
    (hm : 0 < allikvereM0 x) :
    3 * (syracuseStep^[allikvereM0 x - 1]) M + 1 ≤
      3 ^ (allikvereM0 x + 1) * M := by
  have hposodd := allikvereEPrime_mem_pos_odd hM
  let m := allikvereM0 x
  have hiter := syracuse_iterate_le_pow_two (n := M) (t := m - 1)
    hposodd.1 hposodd.2
  have hpowtwo : 4 * 2 ^ (m - 1) ≤ 3 ^ (m + 1) := by
    calc
      4 * 2 ^ (m - 1) = 2 ^ (m + 1) := by rw [show 4 = 2 ^ 2 by norm_num, ← pow_add]; congr 1; omega
      _ ≤ 3 ^ (m + 1) := by
        exact Nat.pow_le_pow_left (show 2 ≤ 3 by omega) (m + 1)
  have hiter' : 3 * (syracuseStep^[m - 1]) M + 1 ≤
      4 * 2 ^ (m - 1) * M := by
    have hMpos : 1 ≤ M := hposodd.1
    have hleft : 3 * (syracuseStep^[m - 1]) M + 1 ≤
        3 * (2 ^ (m - 1) * M) + M := by
      nlinarith [hiter]
    calc
      3 * (syracuseStep^[m - 1]) M + 1 ≤
          3 * (2 ^ (m - 1) * M) + M := hleft
      _ ≤ 4 * 2 ^ (m - 1) * M := by
        have hone : 1 ≤ 2 ^ (m - 1) :=
          Nat.one_le_pow (m - 1) 2 (by omega)
        have hMle : M ≤ 2 ^ (m - 1) * M :=
          by simpa using Nat.mul_le_mul_right M hone
        calc
          3 * (2 ^ (m - 1) * M) + M ≤
              3 * (2 ^ (m - 1) * M) + (2 ^ (m - 1) * M) :=
            Nat.add_le_add_left hMle _
          _ = 4 * 2 ^ (m - 1) * M := by ring
  dsimp [m] at hpowtwo hiter' ⊢
  exact hiter'.trans (Nat.mul_le_mul_right M hpowtwo)

theorem allikvereEPrime_pass_positive_nat {x : ℝ} {M : ℕ}
    (hM : M ∈ allikvereEPrime x) :
    0 < (syracuseStep^[allikvereM0 x]) M := by
  exact (allikvereEPrime_pass_pos_le hM).1

theorem allikvereEPrime_pass_odd {x : ℝ} {M : ℕ}
    (hM : M ∈ allikvereEPrime x) :
    Odd ((syracuseStep^[allikvereM0 x]) M) := by
  have hposodd := allikvereEPrime_mem_pos_odd hM
  exact (syracuse_iterate_pos_odd M hposodd.1 hposodd.2
    (allikvereM0 x)).2

theorem allikvere_prefix_power_lower_bound {x : ℝ} {M : ℕ}
    (hx : 0 ≤ x) (hM : M ∈ allikvereEPrime x)
    (a : Fin (allikvereM0 x) → ℕ) (ha : ∀ i, 0 < a i)
    (hprefix : syracuseExactValuationPrefix M (List.ofFn a)) :
    (3 : ℝ) ^ allikvereM0 x *
        (Real.exp (-(Real.rpow (Real.log x) (7 / 10 : ℝ))) *
          (4 / 3 : ℝ) ^ allikvereM0 x * x) ≤
      (2 : ℝ) ^ (∑ i, a i) * x := by
  have hposodd := allikvereEPrime_mem_pos_odd hM
  have hcoords :=
    (syracuse_exact_prefix_coordinates M (allikvereM0 x) a
      hposodd.1 hposodd.2 ha).mp hprefix
  have hsum :
      (∑ i : Fin (allikvereM0 x), syracuseExponent M i) = ∑ i, a i := by
    apply Finset.sum_congr rfl
    intro i hi
    exact hcoords i
  have haff := syracuse_iterate_affine_numerator M (allikvereM0 x)
    hposodd.1 hposodd.2
  have hnum :
      (3 : ℝ) ^ allikvereM0 x * M ≤
        (2 : ℝ) ^ (∑ i, a i) *
          ((syracuseStep^[allikvereM0 x]) M : ℝ) := by
    have hcast := congrArg (fun n : ℕ => (n : ℝ)) haff
    rw [hsum] at hcast
    have hconst :
        (0 : ℝ) ≤ syracuseAffineConstant
          (List.ofFn (fun i : Fin (allikvereM0 x) => syracuseExponent M i)) := by
      positivity
    have hcast' :
        (2 : ℝ) ^ (∑ i, a i) *
            ((syracuseStep^[allikvereM0 x]) M : ℝ) =
          (3 : ℝ) ^ allikvereM0 x * M +
            (syracuseAffineConstant
              (List.ofFn (fun i : Fin (allikvereM0 x) => syracuseExponent M i)) : ℝ) := by
      simpa [syracuseOrbitValuationList, syracuseAffineNumerator,
        List.length_ofFn, Nat.cast_add,
        Nat.cast_mul, Nat.cast_pow] using hcast
    calc
      (3 : ℝ) ^ allikvereM0 x * M ≤
          (3 : ℝ) ^ allikvereM0 x * M +
            (syracuseAffineConstant
              (List.ofFn (fun i : Fin (allikvereM0 x) => syracuseExponent M i)) : ℝ) := by
                linarith
      _ = (2 : ℝ) ^ (∑ i, a i) *
            ((syracuseStep^[allikvereM0 x]) M : ℝ) := hcast'.symm
  have hpass := allikvereEPrime_pass_pos_le hM
  have hnumx :
      (3 : ℝ) ^ allikvereM0 x * M ≤ (2 : ℝ) ^ (∑ i, a i) * x := by
    exact hnum.trans (mul_le_mul_of_nonneg_left hpass.2 (by positivity))
  have hrange := hM.2.2.1
  have hscaled := mul_le_mul_of_nonneg_left hrange.1
    (by positivity : 0 ≤ (3 : ℝ) ^ allikvereM0 x)
  exact hscaled.trans hnumx

theorem allikvere_exact_prefix_affine_numerator
    {x : ℝ} {M : ℕ}
    (hM : M ∈ allikvereEPrime x)
    (a : Fin (allikvereM0 x) → ℕ) (ha : ∀ i, 0 < a i)
    (hprefix : syracuseExactValuationPrefix M (List.ofFn a)) :
    2 ^ (∑ i, a i) * (syracuseStep^[allikvereM0 x]) M =
      syracuseAffineNumerator (List.ofFn a) M := by
  have hposodd := allikvereEPrime_mem_pos_odd hM
  have hcoords :=
    (syracuse_exact_prefix_coordinates M (allikvereM0 x) a
      hposodd.1 hposodd.2 ha).mp hprefix
  have hlist :
      List.ofFn (fun i : Fin (allikvereM0 x) => syracuseExponent M i) =
        List.ofFn a := by
    have hf : (fun i : Fin (allikvereM0 x) => syracuseExponent M i) = a := by
      funext i
      exact hcoords i
    exact congrArg List.ofFn hf
  have hsum :
      (∑ i : Fin (allikvereM0 x), syracuseExponent M i) = ∑ i, a i := by
    apply Finset.sum_congr rfl
    intro i hi
    exact hcoords i
  have hnum := syracuse_iterate_affine_numerator M (allikvereM0 x)
    hposodd.1 hposodd.2
  simpa [syracuseOrbitValuationList, hlist, hsum] using hnum

/- The following two bounds are the concrete witness inequalities used in the
   source prefix count.  They retain the actual witness `M`; neither theorem
   assumes a bound on an abstract prefix family. -/

def allikverePreviousPrefixSum {x : ℝ}
    (hm : 0 < allikvereM0 x)
    (a : Fin (allikvereM0 x) → ℕ) : ℕ :=
  ∑ i : Fin (allikvereM0 x - 1), a ⟨i.val, by omega⟩

def allikvereLastPrefixExponent {x : ℝ}
    (hm : 0 < allikvereM0 x)
    (a : Fin (allikvereM0 x) → ℕ) : ℕ :=
  a ⟨allikvereM0 x - 1, by omega⟩

def allikverePrefixCoordinateBound (x : ℝ) : ℕ :=
  3 ^ (allikvereM0 x + 1) *
    (Nat.floor
      (Real.exp (Real.rpow (Real.log x) (7 / 10 : ℝ)) *
        (4 / 3 : ℝ) ^ allikvereM0 x * x) + 1)

private theorem nat_le_two_pow (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      have hp : 0 < 2 ^ n := pow_pos (by norm_num) _
      omega

theorem allikvere_admissible_prefix_previous_power_upper_bound
    {x : ℝ} {M : ℕ} (hM : M ∈ allikvereEPrime x)
    (hm : 0 < allikvereM0 x)
    (hthree : (3 : ℝ) ^ allikvereM0 x ≤ x / 2)
    (a : Fin (allikvereM0 x) → ℕ) (ha : ∀ i, 0 < a i)
    (hprefix : syracuseExactValuationPrefix M (List.ofFn a)) :
    (2 : ℝ) ^ allikverePreviousPrefixSum hm a * (x / 2) <
      (3 : ℝ) ^ (allikvereM0 x - 1) * M := by
  have hposodd := allikvereEPrime_mem_pos_odd hM
  have hcoords :=
    (syracuse_exact_prefix_coordinates M (allikvereM0 x) a
      hposodd.1 hposodd.2 ha).mp hprefix
  have hsum :
      (∑ i : Fin (allikvereM0 x - 1), syracuseExponent M i) =
        allikverePreviousPrefixSum hm a := by
    apply Finset.sum_congr rfl
    intro i hi
    exact hcoords ⟨i.val, by omega⟩
  have hbound := allikvere_previous_power_upper_bound hM hm hthree
  simpa [allikverePreviousPrefixSum, hm, hsum] using hbound

theorem allikvere_admissible_prefix_previous_power_scaled
    {x : ℝ} {M : ℕ} (hx : 0 < x)
    (hM : M ∈ allikvereEPrime x)
    (hm : 0 < allikvereM0 x)
    (hthree : (3 : ℝ) ^ allikvereM0 x ≤ x / 2)
    (a : Fin (allikvereM0 x) → ℕ) (ha : ∀ i, 0 < a i)
    (hprefix : syracuseExactValuationPrefix M (List.ofFn a)) :
    (2 : ℝ) ^ allikverePreviousPrefixSum hm a <
      (2 * (3 : ℝ) ^ (allikvereM0 x - 1) * M) / x := by
  have hprev := allikvere_admissible_prefix_previous_power_upper_bound
    hM hm hthree a ha hprefix
  apply (lt_div_iff₀ hx).2
  nlinarith

def allikvereWitnessPreviousBudget (x : ℝ) (M : ℕ) : ℕ :=
  Nat.floor (Real.logb 2
    ((2 : ℝ) * (3 : ℝ) ^ (allikvereM0 x - 1) * M / x))

def allikvereSourcePreviousBudget (x : ℝ) : ℕ :=
  Nat.floor (Real.logb 2
    ((2 : ℝ) * (3 : ℝ) ^ (allikvereM0 x - 1) *
      (Real.exp (Real.rpow (Real.log x) (7 / 10 : ℝ)) *
      (4 / 3 : ℝ) ^ allikvereM0 x * x) / x))

def allikvereSourceLastBudget (x : ℝ) : ℕ :=
  Nat.floor (Real.logb 2
    ((3 : ℝ) ^ (allikvereM0 x + 1) *
      (Real.exp (Real.rpow (Real.log x) (7 / 10 : ℝ)) *
        (4 / 3 : ℝ) ^ allikvereM0 x * x)))

theorem allikvere_admissible_prefix_previous_budget
    {x : ℝ} {M : ℕ} (hx : 0 < x)
    (hM : M ∈ allikvereEPrime x)
    (hm : 0 < allikvereM0 x)
    (hthree : (3 : ℝ) ^ allikvereM0 x ≤ x / 2)
    (a : Fin (allikvereM0 x) → ℕ) (ha : ∀ i, 0 < a i)
    (hprefix : syracuseExactValuationPrefix M (List.ofFn a)) :
    allikverePreviousPrefixSum hm a ≤ allikvereWitnessPreviousBudget x M := by
  have hscaled := allikvere_admissible_prefix_previous_power_scaled
    hx hM hm hthree a ha hprefix
  have hposodd := allikvereEPrime_mem_pos_odd hM
  have hMpos : 0 < (M : ℝ) := by exact_mod_cast hposodd.1
  have hR : 0 <
      (2 : ℝ) * (3 : ℝ) ^ (allikvereM0 x - 1) * M / x := by
    positivity
  have hlog :
      (allikverePreviousPrefixSum hm a : ℝ) <
        Real.logb 2
          ((2 : ℝ) * (3 : ℝ) ^ (allikvereM0 x - 1) * M / x) := by
    apply (Real.lt_logb_iff_rpow_lt (b := (2 : ℝ)) (by norm_num) hR).2
    simpa [Real.rpow_natCast] using hscaled
  simpa [allikvereWitnessPreviousBudget] using (Nat.le_floor hlog.le)

theorem allikvere_admissible_prefix_source_previous_budget
    {x : ℝ} {M : ℕ} (hx : 0 < x)
    (hM : M ∈ allikvereEPrime x)
    (hm : 0 < allikvereM0 x)
    (hthree : (3 : ℝ) ^ allikvereM0 x ≤ x / 2)
    (a : Fin (allikvereM0 x) → ℕ) (ha : ∀ i, 0 < a i)
    (hprefix : syracuseExactValuationPrefix M (List.ofFn a)) :
    allikverePreviousPrefixSum hm a ≤ allikvereSourcePreviousBudget x := by
  have hlocal := allikvere_admissible_prefix_previous_budget
    hx hM hm hthree a ha hprefix
  have hposodd := allikvereEPrime_mem_pos_odd hM
  have hMpos : 0 < (M : ℝ) := by exact_mod_cast hposodd.1
  have hMupper :
      (M : ℝ) ≤
        Real.exp (Real.rpow (Real.log x) (7 / 10 : ℝ)) *
          (4 / 3 : ℝ) ^ allikvereM0 x * x := by
    exact hM.2.2.1.2
  have hlocalpos : 0 <
      (2 : ℝ) * (3 : ℝ) ^ (allikvereM0 x - 1) * M / x := by
    positivity
  have hscaled :
      (2 : ℝ) * (3 : ℝ) ^ (allikvereM0 x - 1) * M ≤
        (2 : ℝ) * (3 : ℝ) ^ (allikvereM0 x - 1) *
          (Real.exp (Real.rpow (Real.log x) (7 / 10 : ℝ)) *
            (4 / 3 : ℝ) ^ allikvereM0 x * x) := by
    gcongr
  have hratio :
      (2 : ℝ) * (3 : ℝ) ^ (allikvereM0 x - 1) * M / x ≤
        (2 : ℝ) * (3 : ℝ) ^ (allikvereM0 x - 1) *
          (Real.exp (Real.rpow (Real.log x) (7 / 10 : ℝ)) *
            (4 / 3 : ℝ) ^ allikvereM0 x * x) / x := by
    exact (div_le_div_iff_of_pos_right hx).2 hscaled
  have hlog := Real.logb_le_logb_of_le (b := (2 : ℝ))
    (by norm_num) hlocalpos hratio
  have hfloor := Nat.floor_mono hlog
  have hfloor' : allikvereWitnessPreviousBudget x M ≤
      allikvereSourcePreviousBudget x := by
    simpa [allikvereWitnessPreviousBudget, allikvereSourcePreviousBudget] using hfloor
  exact hlocal.trans hfloor'

theorem allikvere_admissible_prefix_last_power_upper_bound
    {x : ℝ} {M : ℕ} (hM : M ∈ allikvereEPrime x)
    (hm : 0 < allikvereM0 x)
    (a : Fin (allikvereM0 x) → ℕ) (ha : ∀ i, 0 < a i)
    (hprefix : syracuseExactValuationPrefix M (List.ofFn a)) :
    (2 : ℕ) ^ allikvereLastPrefixExponent hm a ≤
      3 ^ (allikvereM0 x + 1) * M := by
  have hposodd := allikvereEPrime_mem_pos_odd hM
  have hcoords :=
    (syracuse_exact_prefix_coordinates M (allikvereM0 x) a
      hposodd.1 hposodd.2 ha).mp hprefix
  have hlast := syracuse_next_valuation_pow_le_orbit_upper M
    (allikvereM0 x - 1) hposodd.1 hposodd.2
  have hlast' :
      2 ^ a ⟨allikvereM0 x - 1, by omega⟩ ≤
        3 ^ (allikvereM0 x + 1) * M := by
    rw [← hcoords ⟨allikvereM0 x - 1, by omega⟩]
    simpa [show allikvereM0 x - 1 + 2 = allikvereM0 x + 1 by omega] using hlast
  exact hlast'

theorem allikvere_admissible_prefix_source_last_budget
    {x : ℝ} {M : ℕ} (hx : 0 < x)
    (hM : M ∈ allikvereEPrime x)
    (hm : 0 < allikvereM0 x)
    (a : Fin (allikvereM0 x) → ℕ) (ha : ∀ i, 0 < a i)
    (hprefix : syracuseExactValuationPrefix M (List.ofFn a)) :
    allikvereLastPrefixExponent hm a ≤ allikvereSourceLastBudget x := by
  have hlast := allikvere_admissible_prefix_last_power_upper_bound
    hM hm a ha hprefix
  have hupper :
      (M : ℝ) ≤
        Real.exp (Real.rpow (Real.log x) (7 / 10 : ℝ)) *
          (4 / 3 : ℝ) ^ allikvereM0 x * x := by
    exact hM.2.2.1.2
  have hpow :
      (2 : ℝ) ^ allikvereLastPrefixExponent hm a ≤
        (3 : ℝ) ^ (allikvereM0 x + 1) * M := by
    exact_mod_cast hlast
  have hscaled :
      (3 : ℝ) ^ (allikvereM0 x + 1) * M ≤
        (3 : ℝ) ^ (allikvereM0 x + 1) *
          (Real.exp (Real.rpow (Real.log x) (7 / 10 : ℝ)) *
            (4 / 3 : ℝ) ^ allikvereM0 x * x) := by
    gcongr
  have hglobalpos : 0 <
      (3 : ℝ) ^ (allikvereM0 x + 1) *
        (Real.exp (Real.rpow (Real.log x) (7 / 10 : ℝ)) *
          (4 / 3 : ℝ) ^ allikvereM0 x * x) := by
    positivity
  have hpowglobal := hpow.trans hscaled
  have hlog :
      (allikvereLastPrefixExponent hm a : ℝ) ≤
        Real.logb 2
          ((3 : ℝ) ^ (allikvereM0 x + 1) *
            (Real.exp (Real.rpow (Real.log x) (7 / 10 : ℝ)) *
              (4 / 3 : ℝ) ^ allikvereM0 x * x)) := by
    apply (Real.le_logb_iff_rpow_le (b := (2 : ℝ)) (by norm_num)
      hglobalpos).2
    simpa [Real.rpow_natCast] using hpowglobal
  simpa [allikvereSourceLastBudget] using (Nat.le_floor hlog)

theorem allikvere_admissible_prefix_source_budgets
    {x : ℝ} (hx : 0 < x)
    (hm : 0 < allikvereM0 x)
    (hthree : (3 : ℝ) ^ allikvereM0 x ≤ x / 2)
    (a : Fin (allikvereM0 x) → ℕ)
    (ha : allikvereAdmissiblePrefix x a) :
    allikverePreviousPrefixSum hm a ≤ allikvereSourcePreviousBudget x ∧
      allikvereLastPrefixExponent hm a ≤ allikvereSourceLastBudget x := by
  rcases ha with ⟨hapos, M, hM, hprefix⟩
  exact ⟨allikvere_admissible_prefix_source_previous_budget
      hx hM hm hthree a hapos hprefix,
    allikvere_admissible_prefix_source_last_budget
      hx hM hm a hapos hprefix⟩

theorem allikvere_admissible_prefix_bounded_certificate
    {x : ℝ} (hx : 0 < x)
    (hm : 0 < allikvereM0 x)
    (hthree : (3 : ℝ) ^ allikvereM0 x ≤ x / 2)
    (a : Fin (allikvereM0 x) → ℕ)
    (ha : allikvereAdmissiblePrefix x a) :
    ∃ b : AllikvereBoundedPrefixLast
        (allikvereM0 x - 1)
        (allikvereSourcePreviousBudget x)
        (allikvereSourceLastBudget x),
      (∀ i : Fin (allikvereM0 x - 1),
        (b.1 i.castSucc).val = a ⟨i.val, by omega⟩) ∧
      (b.1 (Fin.last (allikvereM0 x - 1))).val =
        allikvereLastPrefixExponent hm a := by
  rcases ha with ⟨hapos, M, hM, hprefix⟩
  have hbud := allikvere_admissible_prefix_source_budgets
    hx hm hthree a ⟨hapos, M, hM, hprefix⟩
  let B := allikvereSourcePreviousBudget x
  let V := allikvereSourceLastBudget x
  have hsub : allikvereM0 x - 1 + 1 = allikvereM0 x :=
    Nat.sub_add_cancel hm
  let f : Fin (allikvereM0 x - 1 + 1) → Fin (max B V + 1) := fun i =>
    ⟨a (Fin.cast hsub i), by
      by_cases hlast : (Fin.cast hsub i).val = allikvereM0 x - 1
      · have hlast' :
            a (Fin.cast hsub i) ≤ V := by
          have hlast'' :
              a ⟨allikvereM0 x - 1, by omega⟩ ≤ V := hbud.2
          have hcastlast :
              Fin.cast hsub i = ⟨allikvereM0 x - 1, by omega⟩ := by
            apply Fin.ext
            exact hlast
          rw [hcastlast]
          exact hlast''
        exact Nat.lt_succ_of_le (hlast'.trans (Nat.le_max_right B V))
      · have hi : (Fin.cast hsub i).val < allikvereM0 x - 1 := by
          have hi' := (Fin.cast hsub i).isLt
          omega
        let j : Fin (allikvereM0 x - 1) :=
          ⟨(Fin.cast hsub i).val, hi⟩
        have hsingle :
            a ⟨j.val, by omega⟩ ≤ allikverePreviousPrefixSum hm a := by
          exact Finset.single_le_sum (f := fun r : Fin (allikvereM0 x - 1) =>
            a ⟨r.val, by omega⟩)
            (fun _ _ => Nat.zero_le _)
            (Finset.mem_univ j)
        have hprefix' : a ⟨j.val, by omega⟩ ≤ B := hsingle.trans hbud.1
        have hcast : a (Fin.cast hsub i) = a ⟨j.val, by omega⟩ := by
          exact congrArg a (Fin.ext (by rfl))
        rw [hcast]
        exact Nat.lt_succ_of_le (hprefix'.trans (Nat.le_max_left B V))⟩
  have hf :
      (∀ i : Fin (allikvereM0 x - 1), 0 < (f i.castSucc).val) ∧
        (∑ i : Fin (allikvereM0 x - 1), (f i.castSucc).val) ≤ B ∧
        (f (Fin.last (allikvereM0 x - 1))).val ≤ V := by
    constructor
    · intro i
      exact hapos ⟨i.val, by omega⟩
    constructor
    · change (∑ i : Fin (allikvereM0 x - 1),
        a (Fin.cast hsub i.castSucc)) ≤ B
      have hsumCast :
          (∑ i : Fin (allikvereM0 x - 1),
              a (Fin.cast hsub i.castSucc)) =
            allikverePreviousPrefixSum hm a := by
        apply Finset.sum_congr rfl
        intro i hi
        congr 1
      rw [hsumCast]
      exact hbud.1
    · change a (Fin.cast hsub (Fin.last (allikvereM0 x - 1))) ≤ V
      have hlastCast :
          Fin.cast hsub (Fin.last (allikvereM0 x - 1)) =
            ⟨allikvereM0 x - 1, by omega⟩ := by
        apply Fin.ext
        rfl
      rw [hlastCast]
      exact hbud.2
  refine ⟨⟨f, hf⟩, ?_, ?_⟩
  · intro i
    dsimp [f]
    exact congrArg a (Fin.ext (by rfl))
  · dsimp [f]
    exact congrArg a (Fin.ext (by rfl))

theorem allikvere_admissible_prefix_coordinate_le
    {x : ℝ} {M : ℕ} (hM : M ∈ allikvereEPrime x)
    (a : Fin (allikvereM0 x) → ℕ) (ha : ∀ i, 0 < a i)
    (hprefix : syracuseExactValuationPrefix M (List.ofFn a)) :
    ∀ i, a i ≤ allikverePrefixCoordinateBound x := by
  have hposodd := allikvereEPrime_mem_pos_odd hM
  have hcoords :=
    (syracuse_exact_prefix_coordinates M (allikvereM0 x) a
      hposodd.1 hposodd.2 ha).mp hprefix
  have hupper :
      (M : ℝ) ≤
        Real.exp (Real.rpow (Real.log x) (7 / 10 : ℝ)) *
          (4 / 3 : ℝ) ^ allikvereM0 x * x := by
    exact hM.2.2.1.2
  have hMfloor : M ≤ Nat.floor
      (Real.exp (Real.rpow (Real.log x) (7 / 10 : ℝ)) *
        (4 / 3 : ℝ) ^ allikvereM0 x * x) := by
    exact Nat.le_floor hupper
  intro i
  have hpow := syracuse_next_valuation_pow_le_orbit_upper M i.val
    hposodd.1 hposodd.2
  have hpow' : 2 ^ a i ≤ 3 ^ (i.val + 2) * M := by
    rw [← hcoords i]
    exact hpow
  have hi : i.val + 2 ≤ allikvereM0 x + 1 := by omega
  have hbase : 3 ^ (i.val + 2) ≤ 3 ^ (allikvereM0 x + 1) := by
    exact Nat.pow_le_pow_right (by omega) hi
  have hpow'' : 2 ^ a i ≤ 3 ^ (allikvereM0 x + 1) * M := by
    exact hpow'.trans (Nat.mul_le_mul_right M hbase)
  have hcoord : a i ≤ 3 ^ (allikvereM0 x + 1) * M :=
    (nat_le_two_pow (a i)).trans hpow''
  have hMbound :
      3 ^ (allikvereM0 x + 1) * M ≤ allikverePrefixCoordinateBound x := by
    dsimp [allikverePrefixCoordinateBound]
    exact Nat.mul_le_mul_left _ (hMfloor.trans (Nat.le_succ _))
  exact hcoord.trans hMbound

theorem allikvere_admissible_prefix_finite
    {x : ℝ} (hx : 0 < x)
    (hm : 0 < allikvereM0 x)
    (hthree : (3 : ℝ) ^ allikvereM0 x ≤ x / 2) :
    Finite {a : Fin (allikvereM0 x) → ℕ // allikvereAdmissiblePrefix x a} := by
  let B := allikverePrefixCoordinateBound x
  let f :
      {a : Fin (allikvereM0 x) → ℕ // allikvereAdmissiblePrefix x a} →
        (Fin (allikvereM0 x) → Fin (B + 1)) := fun a =>
    fun i =>
      ⟨a.1 i, by
        rcases a.2 with ⟨hapos, M, hM, hprefix⟩
        exact Nat.lt_succ_iff.mpr
          (allikvere_admissible_prefix_coordinate_le hM a.1 hapos hprefix i)⟩
  apply Finite.of_injective f
  intro a b hab
  apply Subtype.ext
  funext i
  have hi := congrFun hab i
  exact congrArg Fin.val hi

noncomputable def allikvereAdmissiblePrefixFintype
    (x : ℝ) (hx : 0 < x)
    (hm : 0 < allikvereM0 x)
    (hthree : (3 : ℝ) ^ allikvereM0 x ≤ x / 2) :
    Fintype {a : Fin (allikvereM0 x) → ℕ // allikvereAdmissiblePrefix x a} := by
  letI := allikvere_admissible_prefix_finite hx hm hthree
  exact Fintype.ofFinite _

theorem allikvere_admissible_prefix_card_le_choose
    {x : ℝ} (hx : 0 < x)
    (hm : 0 < allikvereM0 x)
    (hthree : (3 : ℝ) ^ allikvereM0 x ≤ x / 2) :
    @Fintype.card
        {a : Fin (allikvereM0 x) → ℕ // allikvereAdmissiblePrefix x a}
        (allikvereAdmissiblePrefixFintype x hx hm hthree) ≤
      Nat.choose (allikvereSourcePreviousBudget x) (allikvereM0 x - 1) *
        (allikvereSourceLastBudget x + 1) := by
  letI := allikvereAdmissiblePrefixFintype x hx hm hthree
  let Target := AllikvereBoundedPrefixLast
    (allikvereM0 x - 1)
    (allikvereSourcePreviousBudget x)
    (allikvereSourceLastBudget x)
  let cert :
      {a : Fin (allikvereM0 x) → ℕ // allikvereAdmissiblePrefix x a} → Target :=
    fun a => Classical.choose (allikvere_admissible_prefix_bounded_certificate
      hx hm hthree a.1 a.2)
  have hcert (a : {a : Fin (allikvereM0 x) → ℕ // allikvereAdmissiblePrefix x a}) :
      (∀ i : Fin (allikvereM0 x - 1),
        ((cert a).1 i.castSucc).val = a.1 ⟨i.val, by omega⟩) ∧
      ((cert a).1 (Fin.last (allikvereM0 x - 1))).val =
        allikvereLastPrefixExponent hm a.1 := by
    exact Classical.choose_spec (allikvere_admissible_prefix_bounded_certificate
      hx hm hthree a.1 a.2)
  have hinj : Function.Injective cert := by
    intro a b hab
    apply Subtype.ext
    funext i
    by_cases hi : i.val < allikvereM0 x - 1
    · let j : Fin (allikvereM0 x - 1) := ⟨i.val, hi⟩
      have hab' := congrArg (fun c : Target => (c.1 j.castSucc).val) hab
      have ha := (hcert a).1 j
      have hb := (hcert b).1 j
      rw [ha, hb] at hab'
      simpa [j] using hab'
    · have hi' : i = ⟨allikvereM0 x - 1, by omega⟩ := by
        have hival : i.val = allikvereM0 x - 1 := by omega
        exact Fin.ext hival
      have hab' := congrArg
        (fun c : Target => (c.1 (Fin.last (allikvereM0 x - 1))).val) hab
      have ha := (hcert a).2
      have hb := (hcert b).2
      rw [ha, hb] at hab'
      simpa [allikvereLastPrefixExponent, hi'] using hab'
  calc
    @Fintype.card
        {a : Fin (allikvereM0 x) → ℕ // allikvereAdmissiblePrefix x a}
        (allikvereAdmissiblePrefixFintype x hx hm hthree) ≤
        Fintype.card Target := Fintype.card_le_of_injective cert hinj
    _ ≤ Nat.choose (allikvereSourcePreviousBudget x) (allikvereM0 x - 1) *
          (allikvereSourceLastBudget x + 1) := by
      exact allikvere_bounded_prefix_last_card_le_choose
        (allikvereM0 x - 1)
        (allikvereSourcePreviousBudget x)
        (allikvereSourceLastBudget x)


end


/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under GPL-3.0-or-later as described in the file LICENSE.
Authors: Adam McKenna.
-/


set_option autoImplicit false

open Filter Real
open scoped Topology

noncomputable section

/-!
# Scalar subpolynomial absorption for the Allikvere 6.3 parameter

This Mathlib-only helper handles the floor, logarithmic-power, and logarithmic-loss
factors in the numerical part of the later prefix-count argument.  It has no
Syracuse, prefix-count, CRT, probability, or discrepancy assumptions.
-/

private lemma allikvere_scalar_log_ratio_tendsto_zero
    {C D : ℝ} (_hC : 0 ≤ C) (hD : 0 ≤ D) :
    Tendsto (fun L : ℝ =>
      (C * L ^ (7 / 10 : ℝ) + Real.log (D * L + 1)) / L) atTop (𝓝 0) := by
  have hpow : Tendsto (fun L : ℝ => L ^ (7 / 10 : ℝ) / L) atTop (𝓝 0) := by
    have hneg := tendsto_rpow_neg_atTop (y := (3 / 10 : ℝ)) (by norm_num)
    refine hneg.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
    rw [← Real.rpow_sub_one hL.ne']
    norm_num [Real.rpow_one]
  have hCpow : Tendsto (fun L : ℝ => C * L ^ (7 / 10 : ℝ) / L)
    atTop (𝓝 0) := by
    have h := (tendsto_const_nhds (x := C)).mul hpow
    simpa only [div_eq_mul_inv, mul_assoc, mul_zero] using h
  have hlog : Tendsto (fun L : ℝ => Real.log (D * L + 1) / L)
      atTop (𝓝 0) := by
    by_cases hD0 : D = 0
    · simp [hD0]
    · have hDpos : 0 < D := lt_of_le_of_ne hD (Ne.symm hD0)
      have hDL : Tendsto (fun L : ℝ => D * L + 1) atTop atTop := by
        exact tendsto_atTop_add_const_right atTop 1
          (tendsto_id.const_mul_atTop hDpos)
      have hlog_over : Tendsto
          (fun L : ℝ => Real.log (D * L + 1) / (D * L + 1)) atTop (𝓝 0) := by
        simpa [Function.comp_def] using
          (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hDL)
      have hquot : Tendsto (fun L : ℝ => (D * L + 1) / L)
          atTop (𝓝 D) := by
        have h : Tendsto (fun L : ℝ => D + L⁻¹) atTop (𝓝 D) := by
          simpa using (tendsto_const_nhds (x := D)).add tendsto_inv_atTop_zero
        refine h.congr' ?_
        filter_upwards [eventually_ne_atTop (0 : ℝ)] with L hL
        field_simp
      have hprod : Tendsto (fun L : ℝ =>
          Real.log (D * L + 1) / (D * L + 1) * ((D * L + 1) / L))
          atTop (𝓝 0) := by
        simpa using hlog_over.mul hquot
      refine hprod.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
      have hDLpos : 0 < D * L + 1 := by positivity
      field_simp
  have hsum := hCpow.add hlog
  convert hsum using 1
  · funext L
    rw [add_div]
  · simp

private lemma allikvere_scalar_log_absorption
    {C D η : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) (hη : 0 < η) :
    ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L →
      0 < L ∧ C * L ^ (7 / 10 : ℝ) + Real.log (D * L + 1) ≤ η * L := by
  have hratio := allikvere_scalar_log_ratio_tendsto_zero hC hD
  have hev : ∀ᶠ L : ℝ in atTop,
      (C * L ^ (7 / 10 : ℝ) + Real.log (D * L + 1)) / L < η :=
    hratio.eventually (eventually_lt_nhds hη)
  have hpos : ∀ᶠ L : ℝ in atTop, 0 < L := eventually_gt_atTop 0
  obtain ⟨L₀, hL₀⟩ := eventually_atTop.1 (hpos.and hev)
  refine ⟨max L₀ 1, ?_⟩
  intro L hL
  have hL0 := hL₀ L (le_trans (le_max_left L₀ 1) hL)
  have hL1 := hL₀ L (le_trans (le_max_left L₀ 1) hL)
  refine ⟨hL0.1, ?_⟩
  exact (div_lt_iff₀ hL0.1).mp hL1.2 |>.le

theorem allikvere_scalar_subpolynomial_eventually
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) :
    ∃ x₀ : ℝ, 1 < x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
      (4 : ℝ) ^ Nat.floor (Real.log x / 100000) *
          Real.exp (C * (Real.log x) ^ (7 / 10 : ℝ)) *
          (D * Real.log x + 1) ≤ Real.rpow x (1 / 10000 : ℝ) := by
  have hlog4 : Real.log (4 : ℝ) ≤ 3 := by
    calc
      Real.log (4 : ℝ) ≤ (4 : ℝ) - 1 := Real.log_le_sub_one_of_pos (by norm_num)
      _ = 3 := by norm_num
  have hq : Real.log (4 : ℝ) / 100000 < (1 / 10000 : ℝ) := by
    nlinarith
  let η : ℝ := 1 / 10000 - Real.log (4 : ℝ) / 100000
  have hη : 0 < η := by
    dsimp [η]
    linarith
  obtain ⟨L₀, hL₀⟩ := allikvere_scalar_log_absorption hC hD hη
  let L₁ : ℝ := max L₀ 1
  let x₀ : ℝ := Real.exp L₁
  have hL₁ : 0 < L₁ := by
    dsimp [L₁]
    exact lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  refine ⟨x₀, ?_, ?_⟩
  · dsimp [x₀]
    exact (Real.one_lt_exp_iff).2 hL₁
  · intro x hx
    have hx₀ : 0 < x₀ := by
      dsimp [x₀]
      positivity
    have hxpos : 0 < x := lt_of_lt_of_le hx₀ hx
    have hL : L₁ ≤ Real.log x := by
      have := Real.log_le_log (show 0 < Real.exp L₁ by positivity) hx
      simpa [x₀, Real.log_exp] using this
    have hLlarge : L₀ ≤ Real.log x := le_trans (le_max_left _ _) hL
    have hLdata := hL₀ (Real.log x) hLlarge
    have hlogpos : 0 < Real.log x := lt_of_lt_of_le hL₁ hL
    have hfloor : (Nat.floor (Real.log x / 100000) : ℝ) ≤
        Real.log x / 100000 := Nat.floor_le (by positivity)
    have hfour : (4 : ℝ) ^ Nat.floor (Real.log x / 100000) =
        Real.exp (Real.log 4 * (Nat.floor (Real.log x / 100000) : ℝ)) := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num)]
    have hfloor_log :
        Real.log 4 * (Nat.floor (Real.log x / 100000) : ℝ) ≤
          (Real.log 4 / 100000) * Real.log x := by
      have hlog4nonneg : 0 ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num)
      calc
        Real.log 4 * (Nat.floor (Real.log x / 100000) : ℝ) ≤
            Real.log 4 * (Real.log x / 100000) :=
          mul_le_mul_of_nonneg_left hfloor hlog4nonneg
        _ = (Real.log 4 / 100000) * Real.log x := by ring
    have hmain :
        Real.log 4 / 100000 * Real.log x +
            (C * (Real.log x) ^ (7 / 10 : ℝ) +
              Real.log (D * Real.log x + 1)) ≤
          (1 / 10000 : ℝ) * Real.log x := by
      dsimp [η] at hLdata ⊢
      linarith
    have hfactorpos : 0 < D * Real.log x + 1 := by
      have : 0 ≤ D * Real.log x := mul_nonneg hD hlogpos.le
      linarith
    have hfactor : D * Real.log x + 1 =
        Real.exp (Real.log (D * Real.log x + 1)) := by
      rw [Real.exp_log hfactorpos]
    calc
      (4 : ℝ) ^ Nat.floor (Real.log x / 100000) *
          Real.exp (C * (Real.log x) ^ (7 / 10 : ℝ)) *
          (D * Real.log x + 1) =
          Real.exp (Real.log 4 * (Nat.floor (Real.log x / 100000) : ℝ)) *
            (Real.exp (C * (Real.log x) ^ (7 / 10 : ℝ)) *
              Real.exp (Real.log (D * Real.log x + 1))) := by
        rw [hfour]
        conv_lhs => rw [hfactor]
        ring
      _ = Real.exp (Real.log 4 * (Nat.floor (Real.log x / 100000) : ℝ) +
            (C * (Real.log x) ^ (7 / 10 : ℝ) +
              Real.log (D * Real.log x + 1))) := by
        rw [← Real.exp_add, ← Real.exp_add]
      _ ≤ Real.exp ((1 / 10000 : ℝ) * Real.log x) :=
        Real.exp_le_exp.mpr
          (le_trans (add_le_add hfloor_log (le_refl _)) hmain)
      _ = Real.rpow x (1 / 10000 : ℝ) := by
        change Real.exp ((1 / 10000 : ℝ) * Real.log x) =
          x ^ (1 / 10000 : ℝ)
        rw [Real.rpow_def_of_pos hxpos]
        ring_nf


/-!
# Generic eventual bounds for the Allikvere source budgets

This file isolates the numerical source-budget formulas from the E-prime
stopping-set file.  It deliberately imports only Mathlib and the scalar
subpolynomial absorption lemma, so it does not depend on the still-evolving
prefix-count consumer.
-/

set_option autoImplicit false

open Filter Real
open scoped Topology

noncomputable section

def allikvereBudgetM (x : ℝ) : ℕ :=
  Nat.floor (Real.log x / 100000)

def allikvereBudgetQPrev (x : ℝ) : ℝ :=
  (2 : ℝ) * (3 : ℝ) ^ (allikvereBudgetM x - 1) *
    (Real.exp (Real.rpow (Real.log x) (7 / 10 : ℝ)) *
      (4 / 3 : ℝ) ^ allikvereBudgetM x * x) / x

def allikvereBudgetQLast (x : ℝ) : ℝ :=
  (3 : ℝ) ^ (allikvereBudgetM x + 1) *
    (Real.exp (Real.rpow (Real.log x) (7 / 10 : ℝ)) *
      (4 / 3 : ℝ) ^ allikvereBudgetM x * x)

def allikvereBudgetB (x : ℝ) : ℕ :=
  Nat.floor (Real.logb 2 (allikvereBudgetQPrev x))

def allikvereBudgetV (x : ℝ) : ℕ :=
  Nat.floor (Real.logb 2 (allikvereBudgetQLast x))

private lemma allikvere_budget_log_two_lower :
    (1 / 2 : ℝ) ≤ Real.log 2 := by
  have h := Real.le_log_one_add_of_nonneg (x := (1 : ℝ)) (by norm_num)
  linarith

private lemma allikvere_budget_log_three_le_two :
    Real.log 3 ≤ (2 : ℝ) := by
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)
  norm_num at h ⊢
  exact h

private lemma allikvere_budget_log_two_le_one :
    Real.log 2 ≤ (1 : ℝ) := by
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
  norm_num at h ⊢
  exact h

private lemma allikvere_budget_prev_normalize {x : ℝ}
    (hx : 0 < x) (hm : 0 < allikvereBudgetM x) :
    allikvereBudgetQPrev x =
      (2 / 3 : ℝ) * (4 : ℝ) ^ allikvereBudgetM x *
        Real.exp (Real.rpow (Real.log x) (7 / 10 : ℝ)) := by
  unfold allikvereBudgetQPrev
  have h3pow : (3 : ℝ) ^ allikvereBudgetM x =
      (3 : ℝ) ^ (allikvereBudgetM x - 1) * 3 := by
    calc
      (3 : ℝ) ^ allikvereBudgetM x =
          (3 : ℝ) ^ ((allikvereBudgetM x - 1) + 1) := by
            rw [show allikvereBudgetM x - 1 + 1 = allikvereBudgetM x by omega]
      _ = (3 : ℝ) ^ (allikvereBudgetM x - 1) * 3 := by rw [pow_succ]
  rw [div_pow, h3pow]
  field_simp [hx.ne']

private lemma allikvere_budget_last_normalize {x : ℝ} :
    allikvereBudgetQLast x =
      3 * (4 : ℝ) ^ allikvereBudgetM x *
        Real.exp (Real.rpow (Real.log x) (7 / 10 : ℝ)) * x := by
  unfold allikvereBudgetQLast
  have h3pow : (3 : ℝ) ^ (allikvereBudgetM x + 1) =
      (3 : ℝ) ^ allikvereBudgetM x * 3 := by
    rw [pow_succ]
  rw [div_pow, h3pow]
  have h3 : (3 : ℝ) ^ allikvereBudgetM x ≠ 0 := by positivity
  field_simp [h3]

theorem allikvere_source_budget_eventually :
    ∃ x₀ : ℝ, 1 < x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
      0 < Real.log x ∧
      0 < allikvereBudgetM x ∧
      (3 : ℝ) ^ allikvereBudgetM x ≤ x / 2 ∧
      (2 : ℝ) ^ allikvereBudgetB x *
          ((allikvereBudgetV x : ℝ) + 1) ≤
        Real.rpow x (1 / 10000 : ℝ) := by
  obtain ⟨xs, hxs, hs⟩ :=
    allikvere_scalar_subpolynomial_eventually (C := (1 : ℝ)) (D := (7 : ℝ))
      (by norm_num) (by norm_num)
  let xe : ℝ := Real.exp 100000
  let x₀ : ℝ := max xs xe
  refine ⟨x₀, ?_, ?_⟩
  · have hxe : 1 < xe := by
      dsimp [xe]
      exact (Real.one_lt_exp_iff).2 (by norm_num)
    exact lt_of_lt_of_le hxe (le_max_right _ _)
  · intro x hx
    have hxe_pos : 0 < xe := by
      dsimp [xe]
      positivity
    have hxpos : 0 < x :=
      lt_of_lt_of_le hxe_pos (le_trans (le_max_right _ _) hx)
    have hlog : (100000 : ℝ) ≤ Real.log x := by
      have h := Real.log_le_log (show 0 < Real.exp 100000 by positivity)
        (le_trans (le_max_right _ _) hx)
      simpa [xe, Real.log_exp] using h
    have hlogpos : 0 < Real.log x := by linarith
    have hmle : (allikvereBudgetM x : ℝ) ≤ Real.log x / 100000 := by
      exact Nat.floor_le (by positivity)
    have hmpos : 0 < allikvereBudgetM x := by
      have hone : ((1 : ℕ) : ℝ) ≤ Real.log x / 100000 := by linarith
      have hmone : 1 ≤ allikvereBudgetM x :=
        Nat.le_floor (show ((1 : ℕ) : ℝ) ≤ Real.log x / 100000 from hone)
      omega
    have hznonneg : 0 ≤ Real.rpow (Real.log x) (7 / 10 : ℝ) := by
      exact Real.rpow_nonneg hlogpos.le _
    have hzle : Real.rpow (Real.log x) (7 / 10 : ℝ) ≤ Real.log x := by
      have hbase : (1 : ℝ) ≤ Real.log x := by linarith
      simpa [Real.rpow_one] using
        (Real.rpow_le_rpow_of_exponent_le hbase (show (7 / 10 : ℝ) ≤ 1 by norm_num))
    have hlogthree : Real.log 3 ≤ Real.log x := by
      calc
        Real.log 3 ≤ 2 := allikvere_budget_log_three_le_two
        _ ≤ Real.log x := by linarith
    have hlogtwo : (1 / 2 : ℝ) ≤ Real.log 2 :=
      allikvere_budget_log_two_lower
    have hthree_log :
        (allikvereBudgetM x : ℝ) * Real.log 3 ≤ Real.log x - Real.log 2 := by
      have hmthree :
          (allikvereBudgetM x : ℝ) * Real.log 3 ≤
            (Real.log x / 100000) * 2 := by
        calc
          (allikvereBudgetM x : ℝ) * Real.log 3 ≤
              (Real.log x / 100000) * Real.log 3 :=
            mul_le_mul_of_nonneg_right hmle (by positivity)
          _ ≤ (Real.log x / 100000) * 2 :=
            mul_le_mul_of_nonneg_left allikvere_budget_log_three_le_two
              (by positivity)
      have hlogtwole : Real.log 2 ≤ 1 := allikvere_budget_log_two_le_one
      nlinarith
    have hthree :
        (3 : ℝ) ^ allikvereBudgetM x ≤ x / 2 := by
      have hexp :
          Real.exp ((allikvereBudgetM x : ℝ) * Real.log 3) ≤
            Real.exp (Real.log x - Real.log 2) :=
        Real.exp_le_exp.mpr hthree_log
      have hpow3 :
          (3 : ℝ) ^ allikvereBudgetM x =
            Real.exp (Real.log 3 * (allikvereBudgetM x : ℝ)) := by
        rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num)]
      have hright : Real.exp (Real.log x - Real.log 2) = x / 2 := by
        calc
          Real.exp (Real.log x - Real.log 2) =
              Real.exp (Real.log x) / Real.exp (Real.log 2) := by
                rw [Real.exp_sub]
          _ = x / 2 := by rw [Real.exp_log hxpos, Real.exp_log]; norm_num
      calc
        (3 : ℝ) ^ allikvereBudgetM x =
            Real.exp (Real.log 3 * (allikvereBudgetM x : ℝ)) := hpow3
        _ = Real.exp ((allikvereBudgetM x : ℝ) * Real.log 3) := by
          rw [mul_comm]
        _ ≤ Real.exp (Real.log x - Real.log 2) := hexp
        _ = x / 2 := hright
    have hQprevpos : 0 < allikvereBudgetQPrev x := by
      unfold allikvereBudgetQPrev
      positivity
    have hQprevone : (1 : ℝ) ≤ allikvereBudgetQPrev x := by
      rw [allikvere_budget_prev_normalize hxpos hmpos]
      have hpow4 : (4 : ℝ) ≤ (4 : ℝ) ^ allikvereBudgetM x := by
        have hnat : 1 ≤ allikvereBudgetM x := Nat.one_le_iff_ne_zero.mpr hmpos.ne'
        simpa using (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) hnat)
      have hexp : (1 : ℝ) ≤ Real.exp (Real.rpow (Real.log x) (7 / 10 : ℝ)) :=
        Real.one_le_exp hznonneg
      nlinarith
    have hBfloor :
        (allikvereBudgetB x : ℝ) ≤ Real.logb 2 (allikvereBudgetQPrev x) := by
      exact Nat.floor_le
        (Real.logb_nonneg (b := (2 : ℝ)) (by norm_num) hQprevone)
    have hBpow :
        (2 : ℝ) ^ allikvereBudgetB x ≤ allikvereBudgetQPrev x := by
      have h := (Real.le_logb_iff_rpow_le (b := (2 : ℝ)) (by norm_num)
        hQprevpos).1 hBfloor
      simpa [Real.rpow_natCast] using h
    have hBmajor :
        (2 : ℝ) ^ allikvereBudgetB x ≤
          (4 : ℝ) ^ allikvereBudgetM x *
            Real.exp (Real.rpow (Real.log x) (7 / 10 : ℝ)) := by
      rw [allikvere_budget_prev_normalize hxpos hmpos] at hBpow
      calc
        (2 : ℝ) ^ allikvereBudgetB x ≤
            (2 / 3 : ℝ) * (4 : ℝ) ^ allikvereBudgetM x *
              Real.exp (Real.rpow (Real.log x) (7 / 10 : ℝ)) := hBpow
        _ ≤ (4 : ℝ) ^ allikvereBudgetM x *
              Real.exp (Real.rpow (Real.log x) (7 / 10 : ℝ)) := by
          have hnonneg : 0 ≤ (4 : ℝ) ^ allikvereBudgetM x *
              Real.exp (Real.rpow (Real.log x) (7 / 10 : ℝ)) := by positivity
          nlinarith
    have hloglast :
        Real.logb 2 (allikvereBudgetQLast x) ≤ 7 * Real.log x := by
      rw [allikvere_budget_last_normalize]
      have hlogQ :
          Real.log (3 * (4 : ℝ) ^ allikvereBudgetM x *
              Real.exp (Real.rpow (Real.log x) (7 / 10 : ℝ)) * x) =
            Real.log 3 + (allikvereBudgetM x : ℝ) * Real.log 4 +
              Real.rpow (Real.log x) (7 / 10 : ℝ) + Real.log x := by
        rw [Real.log_mul (by positivity) (by positivity),
          Real.log_mul (by positivity) (by positivity),
          Real.log_mul (by positivity) (by positivity), Real.log_pow,
          Real.log_exp]
      rw [Real.logb, hlogQ]
      have hlog4 : Real.log (4 : ℝ) ≤ (3 : ℝ) := by
        have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
        norm_num at h ⊢
        exact h
      have hden : 0 < Real.log 2 := lt_of_lt_of_le (by norm_num) hlogtwo
      have hfirst :
          (allikvereBudgetM x : ℝ) * Real.log 4 / Real.log 2 ≤
            6 * (allikvereBudgetM x : ℝ) := by
        apply (div_le_iff₀ hden).2
        calc
          (allikvereBudgetM x : ℝ) * Real.log 4 ≤
              (allikvereBudgetM x : ℝ) * 3 :=
            mul_le_mul_of_nonneg_left hlog4 (by positivity)
          _ = 6 * (allikvereBudgetM x : ℝ) * (1 / 2 : ℝ) := by ring
          _ ≤ 6 * (allikvereBudgetM x : ℝ) * Real.log 2 := by
            exact mul_le_mul_of_nonneg_left hlogtwo (by positivity)
      have hm6 : 6 * (allikvereBudgetM x : ℝ) ≤ Real.log x := by
        nlinarith [hmle]
      have hsum :
          Real.log 3 + Real.rpow (Real.log x) (7 / 10 : ℝ) + Real.log x ≤
            3 * Real.log x := by
        linarith [hlogthree, hzle]
      have hquot :
          (Real.log 3 + Real.rpow (Real.log x) (7 / 10 : ℝ) + Real.log x) /
              Real.log 2 ≤ 6 * Real.log x := by
        apply (div_le_iff₀ hden).2
        calc
          Real.log 3 + Real.rpow (Real.log x) (7 / 10 : ℝ) + Real.log x ≤
              3 * Real.log x := hsum
          _ ≤ 6 * Real.log x * Real.log 2 := by
            nlinarith
      calc
        (Real.log 3 + (allikvereBudgetM x : ℝ) * Real.log 4 +
            Real.rpow (Real.log x) (7 / 10 : ℝ) + Real.log x) /
              Real.log 2 =
            (allikvereBudgetM x : ℝ) * Real.log 4 / Real.log 2 +
              (Real.log 3 + Real.rpow (Real.log x) (7 / 10 : ℝ) +
                Real.log x) / Real.log 2 := by ring
        _ ≤ 6 * (allikvereBudgetM x : ℝ) + 6 * Real.log x :=
          add_le_add hfirst hquot
        _ ≤ 7 * Real.log x := by linarith
    have hVfloor :
        (allikvereBudgetV x : ℝ) ≤ 7 * Real.log x := by
      have hQlastone : (1 : ℝ) ≤ allikvereBudgetQLast x := by
        rw [allikvere_budget_last_normalize]
        have hxone : (1 : ℝ) ≤ x :=
          (Real.log_nonneg_iff hxpos).mp hlogpos.le
        have hpowone : (1 : ℝ) ≤ (4 : ℝ) ^ allikvereBudgetM x :=
          one_le_pow₀ (by norm_num)
        have hexpone : (1 : ℝ) ≤
            Real.exp (Real.rpow (Real.log x) (7 / 10 : ℝ)) :=
          Real.one_le_exp hznonneg
        have hprod : (1 : ℝ) ≤
            3 * (4 : ℝ) ^ allikvereBudgetM x *
              Real.exp (Real.rpow (Real.log x) (7 / 10 : ℝ)) := by
          have h3 : (1 : ℝ) ≤ 3 := by norm_num
          have h34 : (1 : ℝ) ≤ 3 * (4 : ℝ) ^ allikvereBudgetM x := by
            simpa [mul_assoc] using
              (mul_le_mul h3 hpowone (by norm_num) (by positivity))
          have h34nonneg : 0 ≤ 3 * (4 : ℝ) ^ allikvereBudgetM x := by
            positivity
          exact le_trans h34 (by
            simpa [mul_assoc] using
              (mul_le_mul_of_nonneg_left hexpone h34nonneg))
        simpa using (mul_le_mul hprod hxone (by norm_num) (by positivity))
      exact (Nat.floor_le
        (Real.logb_nonneg (b := (2 : ℝ)) (by norm_num) hQlastone)).trans hloglast
    have hVfactor :
        (allikvereBudgetV x : ℝ) + 1 ≤ 7 * Real.log x + 1 := by linarith
    have hprod :
        (2 : ℝ) ^ allikvereBudgetB x *
            ((allikvereBudgetV x : ℝ) + 1) ≤
          (4 : ℝ) ^ allikvereBudgetM x *
            Real.exp (Real.rpow (Real.log x) (7 / 10 : ℝ)) *
            (7 * Real.log x + 1) := by
      calc
        (2 : ℝ) ^ allikvereBudgetB x *
              ((allikvereBudgetV x : ℝ) + 1) ≤
            ((4 : ℝ) ^ allikvereBudgetM x *
              Real.exp (Real.rpow (Real.log x) (7 / 10 : ℝ))) *
              ((allikvereBudgetV x : ℝ) + 1) := by
          exact mul_le_mul_of_nonneg_right hBmajor (by positivity)
        _ ≤ (4 : ℝ) ^ allikvereBudgetM x *
              Real.exp (Real.rpow (Real.log x) (7 / 10 : ℝ)) *
              (7 * Real.log x + 1) := by
          exact mul_le_mul_of_nonneg_left hVfactor (by positivity)
    have hscalar' := hs x (le_trans (le_max_left _ _) hx)
    have hscalar'' :
        (4 : ℝ) ^ allikvereBudgetM x *
            Real.exp (Real.rpow (Real.log x) (7 / 10 : ℝ)) *
            (7 * Real.log x + 1) ≤ Real.rpow x (1 / 10000 : ℝ) := by
      simpa [allikvereBudgetM, one_mul] using hscalar'
    exact
      (show (0 < Real.log x ∧ 0 < allikvereBudgetM x ∧
        (3 : ℝ) ^ allikvereBudgetM x ≤ x / 2 ∧
        (2 : ℝ) ^ allikvereBudgetB x *
            ((allikvereBudgetV x : ℝ) + 1) ≤
          Real.rpow x (1 / 10000 : ℝ)) from
        ⟨hlogpos, hmpos, hthree, hprod.trans hscalar''⟩)


/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under GPL-3.0-or-later as described in the file LICENSE.
Authors: Adam McKenna.
-/



set_option autoImplicit false

open Nat
open scoped BigOperators

noncomputable section

/-!
# Fixed-prefix interval identification for Allikvere's stopping set

This module treats one full valuation prefix at a time.  It does not assert
that the union `allikvereEPrime` is an interval.
-/

def allikverePrefixList {m : ℕ} (a : Fin m → ℕ) (j : ℕ) (hj : j ≤ m) : List ℕ :=
  List.ofFn (fun i : Fin j => a ⟨i.val, lt_of_lt_of_le i.isLt hj⟩)

def allikverePrefixSum {m : ℕ} (a : Fin m → ℕ) (j : ℕ) (hj : j ≤ m) : ℕ :=
  (allikverePrefixList a j hj).sum

def allikverePrefixConstant {m : ℕ} (a : Fin m → ℕ) (j : ℕ) (hj : j ≤ m) : ℕ :=
  syracuseAffineConstant (allikverePrefixList a j hj)

def allikverePrefixAffineValue {m : ℕ} (a : Fin m → ℕ) (j : ℕ) (hj : j ≤ m)
    (y : ℝ) : ℝ :=
  (3 : ℝ) ^ j * y + allikverePrefixConstant a j hj

def allikvereRangeLower (x : ℝ) (m : ℕ) : ℝ :=
  Real.exp (-(Real.rpow (Real.log x) (7 / 10 : ℝ))) *
    (4 / 3 : ℝ) ^ m * x

def allikvereRangeUpper (x : ℝ) (m : ℕ) : ℝ :=
  Real.exp (Real.rpow (Real.log x) (7 / 10 : ℝ)) *
    (4 / 3 : ℝ) ^ m * x

def allikvereRangeReal (x : ℝ) (m : ℕ) (y : ℝ) : Prop :=
  allikvereRangeLower x m ≤ y ∧ y ≤ allikvereRangeUpper x m

def allikverePrefixAffineWindowReal {m : ℕ} (x : ℝ) (a : Fin m → ℕ) (y : ℝ) : Prop :=
  1 ≤ y ∧
    allikvereRangeReal x m y ∧
    (∀ j : Fin m,
      (2 : ℝ) ^ allikverePrefixSum a j j.isLt.le * x <
        allikverePrefixAffineValue a j j.isLt.le y) ∧
    (2 : ℝ) ^ allikverePrefixSum a m le_rfl ≤
      allikverePrefixAffineValue a m le_rfl y ∧
    allikverePrefixAffineValue a m le_rfl y ≤
      (2 : ℝ) ^ allikverePrefixSum a m le_rfl * x

def allikverePrefixAffineWindowNat {m : ℕ} (x : ℝ) (a : Fin m → ℕ) (M : ℕ) : Prop :=
  allikverePrefixAffineWindowReal x a (M : ℝ)

def allikverePrefixAffineWindowSet {m : ℕ} (x : ℝ) (a : Fin m → ℕ) : Set ℕ :=
  {M | allikverePrefixAffineWindowNat x a M}

private lemma allikverePrefixAffineValue_mono {m : ℕ} (a : Fin m → ℕ)
    (j : ℕ) (hj : j ≤ m) {y₁ y₂ : ℝ} (hy : y₁ ≤ y₂) :
    allikverePrefixAffineValue a j hj y₁ ≤ allikverePrefixAffineValue a j hj y₂ := by
  unfold allikverePrefixAffineValue
  have hpow : 0 ≤ (3 : ℝ) ^ j := pow_nonneg (by norm_num) j
  exact add_le_add (mul_le_mul_of_nonneg_left hy hpow) le_rfl

private lemma allikverePrefixList_eq_of_coords {m j : ℕ} (a : Fin m → ℕ)
    (hjm : j ≤ m) (f : Fin j → ℕ)
    (hf : ∀ i : Fin j, f i = a ⟨i.val, lt_of_lt_of_le i.isLt hjm⟩) :
    List.ofFn f = allikverePrefixList a j hjm := by
  exact congrArg (fun g : Fin j → ℕ => List.ofFn g) (by
    funext i
    exact hf i)

theorem syracuse_iterate_affine_prefix {m M j : ℕ} (a : Fin m → ℕ)
    (hjm : j ≤ m) (hM : 0 < M) (hodd : Odd M)
    (hcoords : ∀ i : Fin m, syracuseExponent M i = a i) :
    (2 : ℝ) ^ allikverePrefixSum a j hjm * ((syracuseStep^[j]) M : ℝ) =
      allikverePrefixAffineValue a j hjm (M : ℝ) := by
  have hlist :
      syracuseOrbitValuationList M j =
        allikverePrefixList a j hjm := by
    unfold syracuseOrbitValuationList
    apply allikverePrefixList_eq_of_coords a hjm
    intro i
    exact hcoords ⟨i.val, lt_of_lt_of_le i.isLt hjm⟩
  have hsum :
      (∑ i : Fin j, syracuseExponent M i) = allikverePrefixSum a j hjm := by
    have hs := congrArg List.sum hlist
    simpa [syracuseOrbitValuationList, allikverePrefixSum, List.sum_ofFn] using hs
  have hnum := syracuse_iterate_affine_numerator M j hM hodd
  rw [hlist] at hnum
  have hreal := congrArg (fun n : ℕ => (n : ℝ)) hnum
  simpa [allikverePrefixAffineValue, allikverePrefixSum, allikverePrefixConstant,
    allikverePrefixList, syracuseAffineNumerator, List.length_ofFn, Nat.cast_mul,
    Nat.cast_pow, hsum] using hreal

theorem odd_of_mod_pow_two_eq_odd {S M r : ℕ} (hr : Odd r)
    (hmod : M % 2 ^ (S + 1) = r) : Odd M := by
  obtain ⟨k, hk⟩ := hr
  have hdecomp := Nat.mod_add_div M (2 ^ (S + 1))
  refine ⟨k + 2 ^ S * (M / 2 ^ (S + 1)), ?_⟩
  calc
    M = M % 2 ^ (S + 1) + 2 ^ (S + 1) * (M / 2 ^ (S + 1)) := hdecomp.symm
    _ = 2 * (k + 2 ^ S * (M / 2 ^ (S + 1))) + 1 := by
      rw [hmod, hk, pow_succ]
      ring

theorem allikverePrefixAffineWindowSet_ordConnected {m : ℕ} (x : ℝ) (a : Fin m → ℕ) :
    (allikverePrefixAffineWindowSet x a).OrdConnected := by
  rw [Set.ordConnected_iff]
  intro M₁ h₁ M₂ h₂ h₁₂ M hM
  have hM₁ : (M₁ : ℝ) ≤ M := by exact_mod_cast hM.1
  have hM₂ : (M : ℝ) ≤ M₂ := by exact_mod_cast hM.2
  have h₁mono (j : Fin m) :=
    allikverePrefixAffineValue_mono a j.val j.isLt.le hM₁
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact le_trans h₁.1 hM₁
  · exact ⟨le_trans h₁.2.1.1 hM₁, le_trans hM₂ h₂.2.1.2⟩
  · intro j
    exact (h₁.2.2.1 j).trans_le (h₁mono j)
  · exact h₁.2.2.2.1.trans (allikverePrefixAffineValue_mono a m le_rfl hM₁)
  · exact (allikverePrefixAffineValue_mono a m le_rfl hM₂).trans h₂.2.2.2.2

theorem allikverePrefixAffineWindowSet_bddAbove {m : ℕ} (x : ℝ) (a : Fin m → ℕ) :
    BddAbove (allikverePrefixAffineWindowSet x a) := by
  refine ⟨⌈allikvereRangeUpper x m⌉₊, ?_⟩
  intro M hM
  have hreal : (M : ℝ) ≤ allikvereRangeUpper x m := hM.2.1.2
  have hceil : allikvereRangeUpper x m ≤ (⌈allikvereRangeUpper x m⌉₊ : ℝ) :=
    Nat.le_ceil _
  exact_mod_cast hreal.trans hceil

/- A reusable closed-interval representative for any bounded order-connected
   subset of `ℕ`; the empty case is kept explicit for consumers. -/
noncomputable def natOrdConnectedInterval (S : Set ℕ) : Set ℕ :=
  by classical exact if hS : S.Nonempty then Set.Icc (sInf S) (sSup S) else ∅

theorem eq_natOrdConnectedInterval {S : Set ℕ} (hS : S.OrdConnected)
    (hUpper : BddAbove S) : S = natOrdConnectedInterval S := by
  by_cases hNonempty : S.Nonempty
  · rw [natOrdConnectedInterval, dif_pos hNonempty]
    exact (hNonempty.ordConnected_iff_of_bdd (OrderBot.bddBelow _)
      hUpper).mp hS
  · rw [natOrdConnectedInterval, dif_neg hNonempty]
    exact Set.not_nonempty_iff_eq_empty.mp hNonempty

def allikvereNatRealPreimage (W : Set ℝ) : Set ℕ :=
  {M | (M : ℝ) ∈ W}

def allikverePrefixWindowSlice {m : ℕ} (x : ℝ) (a : Fin m → ℕ)
    (W : Set ℝ) : Set ℕ :=
  allikverePrefixAffineWindowSet x a ∩ allikvereNatRealPreimage W

theorem allikverePrefixWindowSlice_ordConnected {m : ℕ} (x : ℝ)
    (a : Fin m → ℕ) (W : Set ℝ) (hW : W.OrdConnected) :
    (allikverePrefixWindowSlice x a W).OrdConnected := by
  have hcast : Monotone (fun M : ℕ => (M : ℝ)) := by
    intro M₁ M₂ hM
    change (M₁ : ℝ) ≤ (M₂ : ℝ)
    exact_mod_cast hM
  unfold allikverePrefixWindowSlice allikvereNatRealPreimage
  exact (allikverePrefixAffineWindowSet_ordConnected x a).inter
    (hW.preimage_mono hcast)

theorem allikverePrefixWindowSlice_bddAbove {m : ℕ} (x : ℝ)
    (a : Fin m → ℕ) (W : Set ℝ) :
    BddAbove (allikverePrefixWindowSlice x a W) := by
  obtain ⟨B, hB⟩ := allikverePrefixAffineWindowSet_bddAbove x a
  refine ⟨B, ?_⟩
  intro M hM
  exact hB hM.1

theorem allikverePrefixWindowSlice_eq_interval {m : ℕ} (x : ℝ)
    (a : Fin m → ℕ) (W : Set ℝ) (hW : W.OrdConnected) :
    allikverePrefixWindowSlice x a W =
      natOrdConnectedInterval (allikverePrefixWindowSlice x a W) := by
  exact eq_natOrdConnectedInterval
    (allikverePrefixWindowSlice_ordConnected x a W hW)
    (allikverePrefixWindowSlice_bddAbove x a W)

noncomputable def allikverePrefixAffineWindowInterval {m : ℕ} (x : ℝ)
    (a : Fin m → ℕ) : Set ℕ :=
  by
    classical
    exact if h : (allikverePrefixAffineWindowSet x a).Nonempty then
      Set.Icc (sInf (allikverePrefixAffineWindowSet x a))
        (sSup (allikverePrefixAffineWindowSet x a))
    else Set.Icc 1 0

theorem allikverePrefixAffineWindowSet_eq_interval {m : ℕ} (x : ℝ) (a : Fin m → ℕ) :
    allikverePrefixAffineWindowSet x a = allikverePrefixAffineWindowInterval x a := by
  by_cases hW : (allikverePrefixAffineWindowSet x a).Nonempty
  · rw [allikverePrefixAffineWindowInterval, dif_pos hW]
    exact (hW.ordConnected_iff_of_bdd (OrderBot.bddBelow _)
      (allikverePrefixAffineWindowSet_bddAbove x a)).mp
      (allikverePrefixAffineWindowSet_ordConnected x a)
  · have hEmpty : allikverePrefixAffineWindowSet x a = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hW
    rw [hEmpty, allikverePrefixAffineWindowInterval, dif_neg hW]
    simp

theorem allikvereEPrimePrefix_eq_interval_inter_residue {x : ℝ}
    (hx : 1 < x) (hm : 0 < allikvereM0 x)
    (a : Fin (allikvereM0 x) → ℕ) (ha : ∀ i, 0 < a i) :
    ∃ r : Fin (2 ^ ((∑ i, a i) + 1)),
      Odd r.val ∧
      allikvereEPrimePrefix x a =
        allikverePrefixAffineWindowInterval x a ∩
          {M | M % 2 ^ ((∑ i, a i) + 1) = r.val} := by
  obtain ⟨r, hr, hres⟩ := syracuse_exact_prefix_residue _ a ha
  refine ⟨r, hr, ?_⟩
  rw [← allikverePrefixAffineWindowSet_eq_interval x a]
  ext M
  constructor
  · intro hM
    change M ∈ allikvereEPrime x ∧
      syracuseExactValuationPrefix M (List.ofFn a) at hM
    rcases hM.1 with ⟨hodd, hpos, hrange, hpass⟩
    have hcoords :=
      (syracuse_exact_prefix_coordinates M (allikvereM0 x) a hpos hodd ha).mp hM.2
    have hwindow : allikverePrefixAffineWindowNat x a M := by
      refine ⟨by exact_mod_cast hpos, ?_, ?_, ?_, ?_⟩
      · simpa [allikvereRangeReal, allikvereRangeLower, allikvereRangeUpper,
          allikvereRange5010] using hrange
      · intro j
        have hpassR : x < ((syracuseStep^[j.val]) M : ℝ) := by
          have hpassNat := hpass.1 j.val j.isLt
          exact_mod_cast hpassNat
        have hAff := syracuse_iterate_affine_prefix a j.isLt.le hpos hodd hcoords
        have hmul := mul_lt_mul_of_pos_left hpassR (by positivity :
          0 < (2 : ℝ) ^ allikverePrefixSum a j.val j.isLt.le)
        rw [hAff] at hmul
        exact hmul
      · have hpassR : (1 : ℝ) ≤ ((syracuseStep^[allikvereM0 x]) M : ℝ) := by
          exact_mod_cast hpass.2.1
        have hAff := syracuse_iterate_affine_prefix a le_rfl hpos hodd hcoords
        have hmul := mul_le_mul_of_nonneg_left hpassR (by positivity :
          0 ≤ (2 : ℝ) ^ allikverePrefixSum a (allikvereM0 x) le_rfl)
        rw [hAff] at hmul
        simpa using hmul
      · have hpassR : ((syracuseStep^[allikvereM0 x]) M : ℝ) ≤ x := by
          exact_mod_cast hpass.2.2
        have hAff := syracuse_iterate_affine_prefix a le_rfl hpos hodd hcoords
        have hmul := mul_le_mul_of_nonneg_left hpassR (by positivity :
          0 ≤ (2 : ℝ) ^ allikverePrefixSum a (allikvereM0 x) le_rfl)
        rw [hAff] at hmul
        exact hmul
    refine ⟨hwindow, (hres M hpos hodd).mp hM.2⟩
  · rintro ⟨hwindow, hmod⟩
    have hwindow' : allikverePrefixAffineWindowNat x a M := hwindow
    have hpos : 0 < M := by
      have h := hwindow'.1
      have hMone : 1 ≤ M := by exact_mod_cast h
      omega
    have hodd : Odd M := odd_of_mod_pow_two_eq_odd hr hmod
    have hprefix := (hres M hpos hodd).mpr hmod
    have hcoords :=
      (syracuse_exact_prefix_coordinates M (allikvereM0 x) a hpos hodd ha).mp hprefix
    have hrange : allikvereRange5010 x (allikvereM0 x) M := by
      simpa [allikvereRangeReal, allikvereRangeLower, allikvereRangeUpper,
        allikvereRange5010] using hwindow'.2.1
    have hpass : allikvereFirstPassageAt x (allikvereM0 x) M := by
      refine ⟨?_, ?_, ?_⟩
      · intro j hj
        have hAff := syracuse_iterate_affine_prefix a hj.le hpos hodd hcoords
        have hmul := hwindow'.2.2.1 ⟨j, hj⟩
        rw [← hAff] at hmul
        have hposPow : 0 < (2 : ℝ) ^ allikverePrefixSum a j hj.le :=
          pow_pos (by norm_num) _
        exact (mul_lt_mul_iff_right₀ hposPow).mp hmul
      · have hAff := syracuse_iterate_affine_prefix a le_rfl hpos hodd hcoords
        have hmul := hwindow'.2.2.2.1
        rw [← hAff] at hmul
        have hposPow : 0 < (2 : ℝ) ^ allikverePrefixSum a (allikvereM0 x) le_rfl :=
          pow_pos (by norm_num) _
        have hmul' :
            (2 : ℝ) ^ allikverePrefixSum a (allikvereM0 x) le_rfl * (1 : ℝ) ≤
              (2 : ℝ) ^ allikverePrefixSum a (allikvereM0 x) le_rfl *
                ((syracuseStep^[allikvereM0 x]) M : ℝ) := by
          simpa using hmul
        have hreal : (1 : ℝ) ≤ ((syracuseStep^[allikvereM0 x]) M : ℝ) :=
          (mul_le_mul_iff_right₀ hposPow).mp hmul'
        exact_mod_cast hreal
      · have hAff := syracuse_iterate_affine_prefix a le_rfl hpos hodd hcoords
        have hmul := hwindow'.2.2.2.2
        rw [← hAff] at hmul
        have hposPow : 0 < (2 : ℝ) ^ allikverePrefixSum a (allikvereM0 x) le_rfl :=
          pow_pos (by norm_num) _
        exact (mul_le_mul_iff_right₀ hposPow).mp hmul
    exact ⟨⟨hodd, hpos, hrange, hpass⟩, hprefix⟩

theorem allikvereEPrimePrefix_slice_eq_interval_inter_residue {x : ℝ}
    (hx : 1 < x) (hm : 0 < allikvereM0 x)
    (a : Fin (allikvereM0 x) → ℕ) (ha : ∀ i, 0 < a i)
    (W : Set ℝ) (hW : W.OrdConnected) :
    ∃ r : Fin (2 ^ ((∑ i, a i) + 1)),
      Odd r.val ∧
      allikvereEPrimePrefix x a ∩ allikvereNatRealPreimage W =
        natOrdConnectedInterval (allikverePrefixWindowSlice x a W) ∩
          {M | M % 2 ^ ((∑ i, a i) + 1) = r.val} := by
  obtain ⟨r, hr, hE⟩ :=
    allikvereEPrimePrefix_eq_interval_inter_residue hx hm a ha
  refine ⟨r, hr, ?_⟩
  rw [← allikverePrefixAffineWindowSet_eq_interval x a] at hE
  calc
    allikvereEPrimePrefix x a ∩ allikvereNatRealPreimage W =
        (allikverePrefixAffineWindowSet x a ∩
          {M | M % 2 ^ ((∑ i, a i) + 1) = r.val}) ∩
          allikvereNatRealPreimage W := by rw [hE]
    _ = (allikverePrefixWindowSlice x a W) ∩
          {M | M % 2 ^ ((∑ i, a i) + 1) = r.val} := by
      ext M
      simp only [allikverePrefixWindowSlice, Set.mem_inter_iff]
      tauto
    _ = natOrdConnectedInterval (allikverePrefixWindowSlice x a W) ∩
          {M | M % 2 ^ ((∑ i, a i) + 1) = r.val} := by
      exact congrArg (fun S : Set ℕ =>
        S ∩ {M | M % 2 ^ ((∑ i, a i) + 1) = r.val})
        (allikverePrefixWindowSlice_eq_interval x a W hW)


theorem allikvere_eprime_real_partition
    {x : ℝ}
    (W : Set ℝ) :
    allikvereEPrime x ∩ allikvereRealPreimage W =
      ⋃ a : {a : Fin (allikvereM0 x) → ℕ // allikvereAdmissiblePrefix x a},
        allikvereEPrimePrefix x a.1 ∩ allikvereRealPreimage W := by
  ext M
  constructor
  · rintro ⟨hM, hW⟩
    change (M : ℝ) ∈ W at hW
    let a : Fin (allikvereM0 x) → ℕ :=
      fun i => syracuseExponent M i
    have hposodd := allikvereEPrime_mem_pos_odd hM
    have ha : ∀ i, 0 < a i := by
      intro i
      exact syracuse_exponent_pos M i hposodd.1 hposodd.2
    have hprefix :
        syracuseExactValuationPrefix M (List.ofFn a) := by
      rw [syracuse_exact_prefix_coordinates M (allikvereM0 x) a
        hposodd.1 hposodd.2 ha]
      intro i
      rfl
    have had : allikvereAdmissiblePrefix x a :=
      ⟨ha, M, hM, hprefix⟩
    refine Set.mem_iUnion.2 ⟨⟨a, had⟩, ?_⟩
    exact ⟨⟨hM, hprefix⟩, hW⟩
  · intro h
    rcases Set.mem_iUnion.1 h with ⟨a, ha⟩
    exact ⟨ha.1.1, ha.2⟩

/-- Distinct nonempty exact-prefix classes cannot contain the same source. -/
theorem allikvere_eprime_prefix_pairwise_disjoint
    {x : ℝ}
    {a b : {a : Fin (allikvereM0 x) → ℕ // allikvereAdmissiblePrefix x a}}
    (hab : a ≠ b) :
    Disjoint (allikvereEPrimePrefix x a.1)
      (allikvereEPrimePrefix x b.1) := by
  rw [Set.disjoint_left]
  intro M hMa hMb
  have hposodd := allikvereEPrime_mem_pos_odd hMa.1
  have hca :=
    (syracuse_exact_prefix_coordinates M (allikvereM0 x) a.1
      hposodd.1 hposodd.2 a.2.1).mp hMa.2
  have hcb :=
    (syracuse_exact_prefix_coordinates M (allikvereM0 x) b.1
      hposodd.1 hposodd.2 b.2.1).mp hMb.2
  apply hab
  apply Subtype.ext
  funext i
  exact (hca i).symm.trans (hcb i)

/-- The range condition in E-prime gives a finite Nat upper bound. -/
theorem allikvere_eprime_finite
    {x : ℝ} (hx : 0 < x) : (allikvereEPrime x).Finite := by
  let U : ℕ := Nat.floor
    (Real.exp (Real.rpow (Real.log x) (7 / 10 : ℝ)) *
      (4 / 3 : ℝ) ^ allikvereM0 x * x)
  apply Set.Finite.subset (Set.finite_Iic U)
  intro M hM
  have hupper :
      (M : ℝ) ≤
        Real.exp (Real.rpow (Real.log x) (7 / 10 : ℝ)) *
          (4 / 3 : ℝ) ^ allikvereM0 x * x := hM.2.2.1.2
  exact Nat.le_floor hupper

/-- Intersecting E-prime with any real test set remains finite. -/
theorem allikvere_eprime_real_partition_finite
    {x : ℝ} (hx : 0 < x)
    (hm : 0 < allikvereM0 x)
    (hthree : (3 : ℝ) ^ allikvereM0 x ≤ x / 2)
    (W : Set ℝ) :
    (allikvereEPrime x ∩ allikvereRealPreimage W).Finite := by
  rw [allikvere_eprime_real_partition W]
  letI := allikvereAdmissiblePrefixFintype x hx hm hthree
  apply Set.finite_iUnion
  intro a
  exact (allikvere_eprime_finite hx).subset (by
    intro M hM
    exact hM.1.1)

/-- The same partition after an arbitrary additional Nat-side filter. -/
theorem allikvere_eprime_real_partition_filter
    {x : ℝ} (hm : 0 < allikvereM0 x)
    (W : Set ℝ) (T : Set ℕ) :
    (allikvereEPrime x ∩ allikvereRealPreimage W) ∩ T =
      ⋃ a : {a : Fin (allikvereM0 x) → ℕ // allikvereAdmissiblePrefix x a},
        (allikvereEPrimePrefix x a.1 ∩ allikvereRealPreimage W) ∩ T := by
  ext M
  constructor
  · intro h
    have hbase := h.1
    rw [allikvere_eprime_real_partition W] at hbase
    have hpart :
        M ∈ ⋃ a : {a : Fin (allikvereM0 x) → ℕ // allikvereAdmissiblePrefix x a},
          allikvereEPrimePrefix x a.1 ∩ allikvereRealPreimage W := hbase
    rcases Set.mem_iUnion.1 hpart with ⟨a, ha⟩
    exact Set.mem_iUnion.2 ⟨a, ⟨ha, h.2⟩⟩
  · intro h
    rcases Set.mem_iUnion.1 h with ⟨a, ha⟩
    exact ⟨⟨ha.1.1.1, ha.1.2⟩, ha.2⟩

/-- The finite real-set partition converts cardinality to the disjoint
    prefix-index `finsum`; no interval or residue estimate is assumed here. -/
theorem allikvere_eprime_real_partition_ncard
    {x : ℝ} (hx : 0 < x)
    (hm : 0 < allikvereM0 x)
    (hthree : (3 : ℝ) ^ allikvereM0 x ≤ x / 2)
    (W : Set ℝ) :
    (allikvereEPrime x ∩ allikvereRealPreimage W).ncard =
      ∑ᶠ a : {a : Fin (allikvereM0 x) → ℕ // allikvereAdmissiblePrefix x a},
      (allikvereEPrimePrefix x a.1 ∩ allikvereRealPreimage W).ncard := by
  rw [allikvere_eprime_real_partition W]
  letI := allikvereAdmissiblePrefixFintype x hx hm hthree
  apply Set.ncard_iUnion_of_finite
  · intro a
    exact (allikvere_eprime_finite hx).subset (by
      intro M hM
      exact hM.1.1)
  · intro a b hab
    exact (allikvere_eprime_prefix_pairwise_disjoint hab).mono
      Set.inter_subset_left Set.inter_subset_left

/-- The filtered partition gives the exact finite cardinality sum used by a
    residue consumer. -/
theorem allikvere_eprime_real_partition_filter_ncard
    {x : ℝ} (hx : 0 < x)
    (hm : 0 < allikvereM0 x)
    (hthree : (3 : ℝ) ^ allikvereM0 x ≤ x / 2)
    (W : Set ℝ) (T : Set ℕ) :
    ((allikvereEPrime x ∩ allikvereRealPreimage W) ∩ T).ncard =
      ∑ᶠ a : {a : Fin (allikvereM0 x) → ℕ // allikvereAdmissiblePrefix x a},
        ((allikvereEPrimePrefix x a.1 ∩ allikvereRealPreimage W) ∩ T).ncard := by
  rw [allikvere_eprime_real_partition_filter hm W T]
  letI := allikvereAdmissiblePrefixFintype x hx hm hthree
  apply Set.ncard_iUnion_of_finite
  · intro a
    exact (allikvere_eprime_finite hx).subset (by
      intro M hM
      exact hM.1.1.1)
  · intro a b hab
    exact (allikvere_eprime_prefix_pairwise_disjoint hab).mono
      (Set.inter_subset_left.trans Set.inter_subset_left)
      (Set.inter_subset_left.trans Set.inter_subset_left)


end


/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under GPL-3.0-or-later as described in the file LICENSE.
Authors: Adam McKenna.
-/



set_option autoImplicit false

open Nat
open scoped BigOperators

noncomputable section

/-!
# Allikvere fixed-prefix residue discrepancy

This is the actual per-prefix consumer.  Curie's interval/residue identity
supplies the interval; the CRT adapter then counts a target `3^k` residue
inside that interval, relative to the actual prefix-window cardinality.
-/

/-- A fixed positive valuation prefix has at most-one discrepancy in every
target residue class modulo `3^k`, after restricting to any ordered real
window `W`. -/
theorem allikvere_eprime_prefix_mod_three_discrepancy
    {x : ℝ} (hx1 : 1 < x) (hmpos : 0 < allikvereM0 x)
    (a : Fin (allikvereM0 x) → ℕ) (ha : ∀ i, 0 < a i)
    (W : Set ℝ) (hW : W.OrdConnected) (k : ℕ)
    (targetResidue : Fin (3 ^ k)) :
    |((((allikvereEPrimePrefix x a ∩ allikvereNatRealPreimage W) ∩
          {M | M % 3 ^ k = targetResidue.val}).ncard : ℝ) -
        ((allikvereEPrimePrefix x a ∩ allikvereNatRealPreimage W).ncard : ℝ) /
          (3 ^ k : ℝ))| ≤ 1 := by
  obtain ⟨prefixResidue, _hprefixOdd, hslice⟩ :=
    allikvereEPrimePrefix_slice_eq_interval_inter_residue
      hx1 hmpos a ha W hW
  let S := allikverePrefixWindowSlice x a W
  by_cases hS : S.Nonempty
  · rw [natOrdConnectedInterval, dif_pos hS] at hslice
    let lo : ℕ := sInf S
    let hi : ℕ := sSup S
    have hslice' :
        allikvereEPrimePrefix x a ∩ allikvereNatRealPreimage W =
          Set.Icc lo hi ∩ {M | M % 2 ^ ((∑ i, a i) + 1) = prefixResidue.val} := by
      simpa [S, lo, hi] using hslice
    let step : ℕ := 2 ^ ((∑ i, a i) + 1)
    let q : ℕ := 3 ^ k
    have hstep : 0 < step := by
      dsimp [step]
      positivity
    have hprefix_lt : prefixResidue.val < step := by
      exact prefixResidue.isLt
    have hq : 0 < q := by
      dsimp [q]
      positivity
    have hcop : Nat.Coprime step q := by
      dsimp [step, q]
      exact (((by decide : Nat.Coprime 2 3).pow_left (∑ i, a i + 1)).pow_right k)
    have hI : (Set.Icc lo hi : Set ℕ).Finite := Set.finite_Icc lo hi
    have hbaseFinite :
        (Set.Icc lo hi ∩ {M | M % step = prefixResidue.val}).Finite :=
      hI.subset (by intro M hM; exact hM.1)
    have htargetFinite :
        ((Set.Icc lo hi ∩ {M | M % step = prefixResidue.val}) ∩
          {M | M % q = targetResidue.val}).Finite :=
      hbaseFinite.subset (by intro M hM; exact hM.1)
    have hbaseFinset :
        hbaseFinite.toFinset =
          intervalResidueValues lo hi step prefixResidue.val := by
      ext M
      simp [intervalResidueValues]
    have htargetFinset :
        htargetFinite.toFinset =
          (intervalResidueValues lo hi step prefixResidue.val).filter
            (fun M => M % q = targetResidue.val) := by
      ext M
      simp [intervalResidueValues]
    have hbaseCard :
        (allikvereEPrimePrefix x a ∩ allikvereNatRealPreimage W).ncard =
          (intervalResidueValues lo hi step prefixResidue.val).card := by
      rw [hslice', Set.ncard_eq_toFinset_card _ hbaseFinite, hbaseFinset]
    have htargetCard :
        ((allikvereEPrimePrefix x a ∩ allikvereNatRealPreimage W) ∩
          {M | M % q = targetResidue.val}).ncard =
          ((intervalResidueValues lo hi step prefixResidue.val).filter
            (fun M => M % q = targetResidue.val)).card := by
      rw [hslice', Set.ncard_eq_toFinset_card _ htargetFinite, htargetFinset]
    have hdisc := intervalResidueValues_card_discrepancy
      lo hi step prefixResidue.val q targetResidue.val hstep hprefix_lt hq hcop
    have hmodFilter :
        (intervalResidueValues lo hi step prefixResidue.val).filter
            (fun M => Nat.ModEq q M targetResidue.val) =
          (intervalResidueValues lo hi step prefixResidue.val).filter
            (fun M => M % q = targetResidue.val) := by
      ext M
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hM, hmod⟩
        exact ⟨hM, Nat.mod_eq_of_modEq hmod targetResidue.isLt⟩
      · rintro ⟨hM, hmod⟩
        exact ⟨hM, by
          change M % q = targetResidue.val % q
          rw [Nat.mod_eq_of_lt targetResidue.isLt]
          exact hmod⟩
    rw [htargetCard, hbaseCard]
    rw [← hmodFilter]
    simpa [q] using hdisc
  · rw [natOrdConnectedInterval, dif_neg hS] at hslice
    have hbaseEmpty :
        allikvereEPrimePrefix x a ∩ allikvereNatRealPreimage W = ∅ := by
      simpa using hslice
    rw [hbaseEmpty]
    simp


end


/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under GPL-3.0-or-later as described in the file LICENSE.
Authors: Adam McKenna.
-/



set_option autoImplicit false

open scoped BigOperators

noncomputable section

/-!
# Final finite-sum assembly interface for Allikvere's Lemma 6.3

The exact-prefix partition is combined here with a supplied per-prefix
discrepancy estimate.  The latter is deliberately an input: the arithmetic
progression estimate belongs to its own producer.  The public test set is a
real `OrdConnected` set, as in the source statement.
-/

/-- A unit discrepancy on every exact-prefix slice accumulates by at most the
    number of nonempty prefix classes. -/
theorem allikvere_eprime_real_partition_sum_error
    {x : ℝ} (hx : 0 < x)
    (hm : 0 < allikvereM0 x)
    (hthree : (3 : ℝ) ^ allikvereM0 x ≤ x / 2)
    (W : Set ℝ) (hW : W.OrdConnected) (T : Set ℕ)
    (q : {a : Fin (allikvereM0 x) → ℕ // allikvereAdmissiblePrefix x a} → ℝ)
    (hq : ∀ a,
      |(((allikvereEPrimePrefix x a.1 ∩ allikvereRealPreimage W) ∩ T).ncard : ℝ) -
        q a| ≤ 1) :
    |(((allikvereEPrime x ∩ allikvereRealPreimage W) ∩ T).ncard : ℝ) -
        ∑ᶠ a, q a| ≤
      @Fintype.card
        {a : Fin (allikvereM0 x) → ℕ // allikvereAdmissiblePrefix x a}
        (allikvereAdmissiblePrefixFintype x hx hm hthree) := by
  letI := allikvereAdmissiblePrefixFintype x hx hm hthree
  have hpart := allikvere_eprime_real_partition_filter_ncard hx hm hthree W T
  rw [hpart]
  simp only [finsum_eq_sum_of_fintype]
  rw [Nat.cast_sum]
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ a,
          ((((allikvereEPrimePrefix x a.1 ∩ allikvereRealPreimage W) ∩ T).ncard : ℝ) -
            q a)| ≤
        ∑ a,
          |(((allikvereEPrimePrefix x a.1 ∩ allikvereRealPreimage W) ∩ T).ncard : ℝ) -
            q a| := by
              exact Finset.abs_sum_le_sum_abs
                (fun a : {a : Fin (allikvereM0 x) → ℕ // allikvereAdmissiblePrefix x a} ↦
                  ((((allikvereEPrimePrefix x a.1 ∩ allikvereRealPreimage W) ∩ T).ncard : ℝ) -
                    q a)) Finset.univ
    _ ≤ ∑ _a, (1 : ℝ) := by
      exact Finset.sum_le_sum (fun a _ => hq a)
    _ = Fintype.card {a : Fin (allikvereM0 x) → ℕ // allikvereAdmissiblePrefix x a} := by
      simp

/-- The two modules use the same floor-defined source exponent count. -/
theorem allikvereBudgetM_eq_allikvereM0 (x : ℝ) :
    allikvereBudgetM x = allikvereM0 x := by
  rfl

/-- The Volta previous-coordinate budget is the E-prime source budget. -/
theorem allikvereBudgetB_eq_allikvereSourcePreviousBudget (x : ℝ) :
    allikvereBudgetB x = allikvereSourcePreviousBudget x := by
  unfold allikvereBudgetB allikvereBudgetQPrev allikvereSourcePreviousBudget
  rw [allikvereBudgetM_eq_allikvereM0]

/-- The Volta last-coordinate budget is the E-prime source budget. -/
theorem allikvereBudgetV_eq_allikvereSourceLastBudget (x : ℝ) :
    allikvereBudgetV x = allikvereSourceLastBudget x := by
  unfold allikvereBudgetV allikvereBudgetQLast allikvereSourceLastBudget
  rw [allikvereBudgetM_eq_allikvereM0]

/-- Volta's numerical source-budget estimate transfers to the actual
    admissible exact-prefix subtype used by the E-prime partition. -/
theorem allikvere_admissible_prefix_card_le_rpow_of_budget
    {x : ℝ} (hx : 0 < x)
    (hm : 0 < allikvereM0 x)
    (hthree : (3 : ℝ) ^ allikvereM0 x ≤ x / 2)
    (hnum : (2 : ℝ) ^ allikvereBudgetB x *
        ((allikvereBudgetV x : ℝ) + 1) ≤
      Real.rpow x (1 / 10000 : ℝ)) :
    @Fintype.card
        {a : Fin (allikvereM0 x) → ℕ // allikvereAdmissiblePrefix x a}
        (allikvereAdmissiblePrefixFintype x hx hm hthree) ≤
      Real.rpow x (1 / 10000 : ℝ) := by
  have hcard := allikvere_admissible_prefix_card_le_choose
    (x := x) hx hm hthree
  have hpow := allikvere_bounded_prefix_last_card_le_pow
    (allikvereM0 x - 1)
    (allikvereSourcePreviousBudget x)
    (allikvereSourceLastBudget x)
  have hcardNat :
      @Fintype.card
          {a : Fin (allikvereM0 x) → ℕ // allikvereAdmissiblePrefix x a}
          (allikvereAdmissiblePrefixFintype x hx hm hthree) ≤
        2 ^ allikvereSourcePreviousBudget x *
          (allikvereSourceLastBudget x + 1) := by
    calc
      @Fintype.card
          {a : Fin (allikvereM0 x) → ℕ // allikvereAdmissiblePrefix x a}
          (allikvereAdmissiblePrefixFintype x hx hm hthree) ≤
          Nat.choose (allikvereSourcePreviousBudget x) (allikvereM0 x - 1) *
            (allikvereSourceLastBudget x + 1) := hcard
      _ ≤ 2 ^ allikvereSourcePreviousBudget x *
            (allikvereSourceLastBudget x + 1) := by
        exact Nat.mul_le_mul_right _ (Nat.choose_le_two_pow _ _)
  have hcardReal :
      (@Fintype.card
          {a : Fin (allikvereM0 x) → ℕ // allikvereAdmissiblePrefix x a}
          (allikvereAdmissiblePrefixFintype x hx hm hthree) : ℝ) ≤
        ((2 ^ allikvereSourcePreviousBudget x *
          (allikvereSourceLastBudget x + 1) : ℕ) : ℝ) := by
    exact_mod_cast hcardNat
  calc
    (@Fintype.card
        {a : Fin (allikvereM0 x) → ℕ // allikvereAdmissiblePrefix x a}
        (allikvereAdmissiblePrefixFintype x hx hm hthree) : ℝ) ≤
        ((2 ^ allikvereSourcePreviousBudget x *
          (allikvereSourceLastBudget x + 1) : ℕ) : ℝ) := hcardReal
    _ = (2 : ℝ) ^ allikvereBudgetB x *
          ((allikvereBudgetV x : ℝ) + 1) := by
      rw [allikvereBudgetB_eq_allikvereSourcePreviousBudget,
        allikvereBudgetV_eq_allikvereSourceLastBudget]
      norm_num
    _ ≤ Real.rpow x (1 / 10000 : ℝ) := hnum


end


theorem solution :
    ∃ x₀ : ℝ, 1 < x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ W : Set ℝ, W.OrdConnected →
      ∀ k : ℕ, ∀ r : Fin (3 ^ k),
        |((((allikvereEPrime x ∩ allikvereRealPreimage W) ∩
            {M | M % 3 ^ k = r.val}).ncard : ℝ) -
          ((allikvereEPrime x ∩ allikvereRealPreimage W).ncard : ℝ) /
            (3 ^ k : ℝ))| ≤ Real.rpow x (1 / 10000 : ℝ) := by
  obtain ⟨x₀, hx₀, hbudget⟩ := allikvere_source_budget_eventually
  refine ⟨x₀, hx₀, ?_⟩
  intro x hx W hW k r
  have hx1 : 1 < x := lt_of_lt_of_le hx₀ hx
  have hxpos : 0 < x := lt_trans zero_lt_one hx1
  obtain ⟨_hlog, hmBudget, hthreeBudget, hnum⟩ := hbudget x hx
  have hm : 0 < allikvereM0 x := by
    simpa [allikvereBudgetM_eq_allikvereM0] using hmBudget
  have hthree : (3 : ℝ) ^ allikvereM0 x ≤ x / 2 := by
    simpa [allikvereBudgetM_eq_allikvereM0] using hthreeBudget
  letI := allikvereAdmissiblePrefixFintype x hxpos hm hthree
  let T : Set ℕ := {M | M % 3 ^ k = r.val}
  let q :
      {a : Fin (allikvereM0 x) → ℕ // allikvereAdmissiblePrefix x a} → ℝ :=
    fun a =>
      ((allikvereEPrimePrefix x a.1 ∩ allikvereNatRealPreimage W).ncard : ℝ) /
        (3 ^ k : ℝ)
  have hpreimage : allikvereRealPreimage W = allikvereNatRealPreimage W := by
    rfl
  have hq : ∀ a,
      |(((allikvereEPrimePrefix x a.1 ∩ allikvereRealPreimage W) ∩ T).ncard : ℝ) -
        q a| ≤ 1 := by
    intro a
    have hdisc := allikvere_eprime_prefix_mod_three_discrepancy
      hx1 hm a.1 a.2.1 W hW k r
    rw [hpreimage]
    simpa [q, T] using hdisc
  have herror := allikvere_eprime_real_partition_sum_error
    hxpos hm hthree W hW T q hq
  have hpart := allikvere_eprime_real_partition_ncard
    hxpos hm hthree W
  have hpartReal :
      ((allikvereEPrime x ∩ allikvereRealPreimage W).ncard : ℝ) =
        ∑ a : {a : Fin (allikvereM0 x) → ℕ // allikvereAdmissiblePrefix x a},
          ((allikvereEPrimePrefix x a.1 ∩ allikvereRealPreimage W).ncard : ℝ) := by
    rw [hpart]
    simp only [finsum_eq_sum_of_fintype]
    rw [Nat.cast_sum]
  have hpartRealNat :
      ((allikvereEPrime x ∩ allikvereNatRealPreimage W).ncard : ℝ) =
        ∑ a : {a : Fin (allikvereM0 x) → ℕ // allikvereAdmissiblePrefix x a},
          ((allikvereEPrimePrefix x a.1 ∩ allikvereNatRealPreimage W).ncard : ℝ) := by
    simpa [hpreimage] using hpartReal
  have hsumq :
      (∑ᶠ a : {a : Fin (allikvereM0 x) → ℕ // allikvereAdmissiblePrefix x a}, q a) =
        ((allikvereEPrime x ∩ allikvereRealPreimage W).ncard : ℝ) /
          (3 ^ k : ℝ) := by
    simp only [finsum_eq_sum_of_fintype]
    dsimp [q]
    rw [← Finset.sum_div, ← hpartRealNat, ← hpreimage]
  have hcard := allikvere_admissible_prefix_card_le_rpow_of_budget
    hxpos hm hthree hnum
  rw [hsumq] at herror
  simpa [T] using herror.trans hcard


end


#print axioms solution
end
