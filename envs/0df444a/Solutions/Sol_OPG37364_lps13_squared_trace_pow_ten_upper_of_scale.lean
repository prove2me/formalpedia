-- Prove2me | solution 1 for OPG37364.lps13_squared_trace_pow_ten_upper_of_scale
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-09-12T08:49:43.405772+00:00
-- url     : https://prove2.me/submissions/6cf127fd-2717-4e1b-8d00-4d292900a538

/- OPG37364 Stage 17B arithmetic trace estimate.
Replays previously proved LPS word/trace infrastructure, including Stage 15
e7da13e5-b5dc-41cb-87d4-7fe6d2852aa2 and Stage 16
d6ef945a-58ff-41b6-a2cb-31c91ee913a8. These classical ingredients are not
claimed as new mathematics. All proof bodies are present; no imported oracle.
No CFSG, connectedness, or unproved spectral/existence theorem is imported.
-/
import Definitions.Def_opg37364_lps13
import Definitions.Def_opg37364_lps13_eigenspaces
import Definitions.Def_opg37364_lps13_trace
import Definitions.Def_opg37364_lps13_words
import Mathlib.Algebra.Prime.Lemmas
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.ModEq
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Induction
import Mathlib.Data.Nat.Sqrt
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.Coset.Card
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.RingTheory.UniqueFactorizationDomain.Finite
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section Stage17BSource0
-- Source: Verification.Stage17TwoSquareProbe
set_option autoImplicit false
noncomputable section

/-! Exploratory interface probe. This file does not claim a representation-count bound. -/
namespace OPG37364.Stage17Probe

def twoSquarePairs (N : ℕ) : Finset (ℤ × ℤ) :=
  ((Finset.Icc (-(N : ℤ)) N).product (Finset.Icc (-(N : ℤ)) N)).filter
    fun xy => xy.1^2 + xy.2^2 = (N : ℤ)

def r2 (N : ℕ) : ℕ := (twoSquarePairs N).card

theorem mem_twoSquarePairs (N : ℕ) (xy : ℤ × ℤ) :
    xy ∈ twoSquarePairs N ↔ xy.1^2 + xy.2^2 = (N : ℤ) := by
  rcases xy with ⟨x, y⟩
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    have hN : (0 : ℤ) ≤ N := by positivity
    have hx := sq_nonneg x
    have hy := sq_nonneg y
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩,
      Finset.mem_Icc.mpr ⟨?_, ?_⟩⟩, h⟩ <;> nlinarith

def pairEquivNormFiber (N : ℕ) :
    {xy // xy ∈ twoSquarePairs N} ≃ {z : GaussianInt // z.norm = (N : ℤ)} where
  toFun xy := ⟨⟨xy.val.1, xy.val.2⟩, by
    have h := (mem_twoSquarePairs N xy.val).mp xy.property
    simpa [Zsqrtd.norm, pow_two] using h⟩
  invFun z := ⟨(z.val.re, z.val.im), by
    apply (mem_twoSquarePairs N _).mpr
    simpa [Zsqrtd.norm, pow_two] using z.property⟩
  left_inv xy := by rfl
  right_inv z := by rfl

example : EuclideanDomain GaussianInt := inferInstance
example : UniqueFactorizationMonoid GaussianInt := inferInstance

example (N : ℕ) : Finite {z : GaussianInt // z.norm = (N : ℤ)} :=
  Finite.of_equiv {xy // xy ∈ twoSquarePairs N} (pairEquivNormFiber N)

theorem r2_eq_normFiber_card (N : ℕ) :
    r2 N = Nat.card {z : GaussianInt // z.norm = (N : ℤ)} := by
  rw [← Nat.card_congr (pairEquivNormFiber N)]
  simp [r2]

theorem r2_zero : r2 0 = 1 := by
  apply Finset.card_eq_one.mpr
  refine ⟨(0, 0), ?_⟩
  ext ⟨x, y⟩
  rw [mem_twoSquarePairs, Finset.mem_singleton]
  simp only [Prod.mk.injEq, Nat.cast_zero]
  constructor
  · intro h
    constructor <;> nlinarith [sq_nonneg x, sq_nonneg y]
  · rintro ⟨rfl, rfl⟩
    norm_num


end OPG37364.Stage17Probe

end

end Stage17BSource0

noncomputable section Stage17BSource1
-- Source: OPG37364.GaussianDivisorCount
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace OPG37364.GaussianCount

abbrev A := Associates GaussianInt

local instance : Fintype Aˣ := Fintype.ofFinite _

def divCount (a : A) : ℕ := Nat.card {d : A // d ∣ a}

theorem divCount_mul_le (a b : A) (ha : a ≠ 0) (hb : b ≠ 0) :
    divCount (a*b) ≤ divCount a * divCount b := by
  letI := UniqueFactorizationMonoid.fintypeSubtypeDvd a ha
  letI := UniqueFactorizationMonoid.fintypeSubtypeDvd b hb
  let f : ({d : A // d ∣ a} × {d : A // d ∣ b}) → {d : A // d ∣ a*b} :=
    fun x => ⟨x.1.val*x.2.val, mul_dvd_mul x.1.property x.2.property⟩
  have hf : Function.Surjective f := by
    intro d
    obtain ⟨x,y,hx,hy,hxy⟩ := exists_dvd_and_dvd_of_dvd_mul d.property
    exact ⟨(⟨x,hx⟩,⟨y,hy⟩), Subtype.ext hxy.symm⟩
  simpa [divCount, Nat.card_prod] using Nat.card_le_card_of_surjective f hf

theorem divCount_good_pow (a : A) (ha : a = 1 ∨ Prime a) (e : ℕ) :
    divCount (a^e) ≤ e+1 := by
  let f : Fin (e+1) → {d : A // d ∣ a^e} :=
    fun k => ⟨a^k.val, pow_dvd_pow a (by omega)⟩
  have hf : Function.Surjective f := by
    intro d
    rcases ha with rfl | ha
    · have hd : d.val = 1 := by
        have hu : IsUnit d.val := isUnit_iff_dvd_one.mpr (by simpa using d.property)
        exact isUnit_iff_eq_one.mp hu
      exact ⟨⟨0,by omega⟩, Subtype.ext (by simpa [f] using hd.symm)⟩
    · obtain ⟨k,hk,hdk⟩ := (dvd_prime_pow ha e).mp d.property
      exact ⟨⟨k,by omega⟩, Subtype.ext (associated_iff_eq.mp hdk).symm⟩
  simpa [divCount] using Nat.card_le_card_of_surjective f hf

theorem prime_of_norm_prime (z : GaussianInt) (p : ℕ) (hp : p.Prime)
    (hz : z.norm = (p : ℤ)) : Prime z := by
  apply irreducible_iff_prime.mp
  refine ⟨?_, ?_⟩
  · intro hu
    have := Zsqrtd.norm_eq_one_iff.mpr hu
    rw [hz, Int.natAbs_natCast] at this
    exact hp.ne_one this
  · intro a b hab
    have hn : a.norm.natAbs * b.norm.natAbs = p := by
      rw [← Int.natAbs_mul, ← Zsqrtd.norm_mul, ← hab, hz, Int.natAbs_natCast]
    have h := hp.isUnit_or_isUnit hn.symm
    simpa [← Zsqrtd.norm_eq_one_iff, Nat.isUnit_iff] using h

theorem rational_prime_two_factors (p : ℕ) (hp : p.Prime) :
    ∃ a b : A, Associates.mk (p : GaussianInt) = a*b ∧
      (a = 1 ∨ Prime a) ∧ (b = 1 ∨ Prime b) := by
  by_cases hir : Irreducible (p : GaussianInt)
  · exact ⟨Associates.mk (p : GaussianInt),1,by simp,
      Or.inr (Associates.prime_mk.mpr (irreducible_iff_prime.mp hir)),Or.inl rfl⟩
  · letI : Fact p.Prime := ⟨hp⟩
    obtain ⟨x,y,hxy⟩ := GaussianInt.sq_add_sq_of_nat_prime_of_not_irreducible p hir
    let z : GaussianInt := ⟨x,y⟩
    have hz : z.norm = (p : ℤ) := by
      change (x : ℤ)*(x : ℤ) - (-1)*(y : ℤ)*(y : ℤ) = p
      simp only [neg_mul, one_mul, sub_neg_eq_add]
      exact_mod_cast (by nlinarith [hxy] : x*x+y*y=p)
    have hz' := prime_of_norm_prime z p hp hz
    refine ⟨Associates.mk z, Associates.mk (star z), ?_,
      Or.inr (Associates.prime_mk.mpr hz'),
      Or.inr (Associates.prime_mk.mpr (prime_of_norm_prime (star z) p hp (by simpa using hz)))⟩
    rw [Associates.mk_mul_mk, ← Zsqrtd.norm_eq_mul_conj, hz]
    simp

theorem divCount_rational_prime_pow (p e : ℕ) (hp : p.Prime) :
    divCount (Associates.mk ((p : GaussianInt)^e)) ≤ (e+1)^2 := by
  obtain ⟨a,b,hab,ha,hb⟩ := rational_prime_two_factors p hp
  have hp0 : Associates.mk (p : GaussianInt) ≠ 0 :=
    Associates.mk_ne_zero.mpr (Nat.cast_ne_zero.mpr hp.ne_zero)
  have hab0 : a*b ≠ 0 := hab ▸ hp0
  rw [Associates.mk_pow, hab, mul_pow]
  calc
    divCount (a^e*b^e) ≤ divCount (a^e)*divCount (b^e) :=
      divCount_mul_le _ _ (pow_ne_zero _ (left_ne_zero_of_mul hab0))
        (pow_ne_zero _ (right_ne_zero_of_mul hab0))
    _ ≤ (e+1)*(e+1) := Nat.mul_le_mul (divCount_good_pow a ha e) (divCount_good_pow b hb e)
    _ = (e+1)^2 := by ring

theorem divCount_nat_le (n : ℕ) (hn : 0 < n) :
    divCount (Associates.mk (n : GaussianInt)) ≤ n.divisors.card^2 := by
  induction n using Nat.recOnPrimeCoprime with
  | zero => omega
  | prime_pow p e hp =>
    simpa [Nat.cast_pow, Nat.divisors_prime_pow hp] using divCount_rational_prime_pow p e hp
  | coprime a b ha hb hab iha ihb =>
    rw [Nat.cast_mul, ← Associates.mk_mul_mk, hab.card_divisors_mul, mul_pow]
    exact (divCount_mul_le _ _
      (Associates.mk_ne_zero.mpr (Nat.cast_ne_zero.mpr (by omega)))
      (Associates.mk_ne_zero.mpr (Nat.cast_ne_zero.mpr (by omega)))).trans
      (Nat.mul_le_mul (iha (by omega)) (ihb (by omega)))

def unitBox : Finset (ℤ × ℤ) := (Finset.Icc (-1) 1).product (Finset.Icc (-1) 1)

def unitToBox (u : GaussianIntˣ) : {xy // xy ∈ unitBox} :=
  ⟨((u : GaussianInt).re, (u : GaussianInt).im), by
    have hn := (Zsqrtd.norm_eq_one_iff' (by decide : (-1 : ℤ) ≤ 0) (u : GaussianInt)).mpr u.isUnit
    have he : (u : GaussianInt).re^2 + (u : GaussianInt).im^2 = 1 := by
      simpa [Zsqrtd.norm, pow_two] using hn
    apply Finset.mem_product.mpr
    constructor <;> apply Finset.mem_Icc.mpr <;>
      constructor <;> nlinarith [sq_nonneg (u : GaussianInt).re, sq_nonneg (u : GaussianInt).im]⟩

theorem unitToBox_injective : Function.Injective unitToBox := by
  intro u v huv
  apply Units.ext
  have h := congrArg Subtype.val huv
  exact Zsqrtd.ext (congrArg Prod.fst h) (congrArg Prod.snd h)

instance : Finite GaussianIntˣ := Finite.of_injective unitToBox unitToBox_injective

theorem card_units_le : Nat.card GaussianIntˣ ≤ 9 := by
  have h := Nat.card_le_card_of_injective unitToBox unitToBox_injective
  have hc : Nat.card {xy // xy ∈ unitBox} = 9 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    norm_num [unitBox, Finset.card_product]
    decide
  exact h.trans_eq hc

theorem gaussian_divisor_count_le (n : ℕ) (hn : 0 < n) :
    Nat.card {z : GaussianInt // z ∣ (n : GaussianInt)} ≤ 9*n.divisors.card^2 := by
  letI : Fintype GaussianIntˣ := Fintype.ofFinite _
  let a : A := Associates.mk (n : GaussianInt)
  have ha : a ≠ 0 := Associates.mk_ne_zero.mpr (Nat.cast_ne_zero.mpr hn.ne')
  letI := UniqueFactorizationMonoid.fintypeSubtypeDvd a ha
  let rep (d : {d : A // d ∣ a}) : GaussianInt := Quot.out d.val
  have hrep (d : {d : A // d ∣ a}) : rep d ∣ (n : GaussianInt) := by
    apply Associates.mk_dvd_mk.mp
    simpa only [rep, Associates.quot_out] using d.property
  let f : (GaussianIntˣ × {d : A // d ∣ a}) →
      {z : GaussianInt // z ∣ (n : GaussianInt)} := fun x =>
    ⟨(x.1 : GaussianInt)*rep x.2, by
      simpa only [one_mul] using mul_dvd_mul
        (show (x.1 : GaussianInt) ∣ (1 : GaussianInt) from x.1.isUnit.dvd) (hrep x.2)⟩
  have hf : Function.Surjective f := by
    intro z
    let d : {d : A // d ∣ a} := ⟨Associates.mk z.val, Associates.mk_dvd_mk.mpr z.property⟩
    obtain ⟨u,hu⟩ := Associates.mk_quot_out z.val
    refine ⟨(u,d), Subtype.ext ?_⟩
    simpa only [f, rep, d, mul_comm] using hu
  calc
    Nat.card {z : GaussianInt // z ∣ (n : GaussianInt)} ≤
        Nat.card (GaussianIntˣ × {d : A // d ∣ a}) := Nat.card_le_card_of_surjective f hf
    _ = Nat.card GaussianIntˣ * divCount a := by rw [Nat.card_prod]; rfl
    _ ≤ 9*n.divisors.card^2 := Nat.mul_le_mul card_units_le (divCount_nat_le n hn)

theorem twoSquare_count_le_nine_mul_divisors_sq (n : ℕ) (hn : 0 < n) :
    Stage17Probe.r2 n ≤ 9*n.divisors.card^2 := by
  letI : Fintype GaussianIntˣ := Fintype.ofFinite _
  letI := UniqueFactorizationMonoid.fintypeSubtypeDvd (n : GaussianInt)
    (Nat.cast_ne_zero.mpr hn.ne')
  let f : {z : GaussianInt // z.norm = (n : ℤ)} →
      {z : GaussianInt // z ∣ (n : GaussianInt)} := fun z =>
    ⟨z.val, ⟨star z.val, by rw [← Zsqrtd.norm_eq_mul_conj, z.property]; simp⟩⟩
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z : {z : GaussianInt // z ∣ (n : GaussianInt)} => z.val) h
  rw [Stage17Probe.r2_eq_normFiber_card]
  exact (Nat.card_le_card_of_injective f hf).trans (gaussian_divisor_count_le n hn)

end OPG37364.GaussianCount

end

end Stage17BSource1

noncomputable section Stage17BSource2
-- Source: OPG37364.DivisorFifthBound
set_option autoImplicit false
open scoped BigOperators

namespace OPG37364.DivisorBound

theorem exponent_large_base (e : ℕ) : (e + 1)^5 ≤ 32^e := by
  calc
    (e + 1)^5 ≤ (2^e)^5 := Nat.pow_le_pow_left (Nat.succ_le_of_lt Nat.lt_two_pow_self) 5
    _ = 32^e := by rw [← pow_mul, Nat.mul_comm e 5, pow_mul]; norm_num

theorem exponent_small_base (e : ℕ) : (e + 1)^5 ≤ 512 * 2^e := by
  induction e using Nat.strong_induction_on with
  | h e ih =>
    by_cases he : e ≤ 6
    · interval_cases e <;> norm_num
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (show 7 ≤ e by omega)
      have hprev := ih (6+k) (by omega)
      have hstep : (k+8)^5 ≤ 2*(k+7)^5 := by ring_nf; omega
      calc
        (7+k+1)^5 ≤ 2*(6+k+1)^5 := by simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hstep
        _ ≤ 2*(512*2^(6+k)) := Nat.mul_le_mul_left 2 hprev
        _ = 512*2^(7+k) := by rw [show 7+k=(6+k)+1 by omega, pow_succ]; ring

theorem prime_exponent (p e : ℕ) (hp : p.Prime) :
    (e+1)^5 ≤ (if p < 32 then 512 else 1) * p^e := by
  split_ifs with h
  · exact (exponent_small_base e).trans (Nat.mul_le_mul_left 512
      (Nat.pow_le_pow_left hp.two_le e))
  · simpa using (exponent_large_base e).trans (Nat.pow_le_pow_left (by omega : 32 ≤ p) e)

end OPG37364.DivisorBound

namespace OPG37364

/-- An explicit fifth-power bound for the number of positive divisors. -/
theorem card_divisors_pow_five_le (n : ℕ) (hn : 0 < n) :
    n.divisors.card ^ 5 ≤ 512^32 * n := by
  classical
  have hc : (n.primeFactors.filter (· < 32)).card ≤ 32 := by
    simpa using Finset.card_le_card (show n.primeFactors.filter (· < 32) ⊆
      Finset.range 32 from fun p hp => Finset.mem_range.mpr (Finset.mem_filter.mp hp).2)
  have hprod : (∏ p ∈ n.primeFactors, (if p < 32 then 512 else 1 : ℕ)) =
      512 ^ (n.primeFactors.filter (· < 32)).card := by
    rw [← Finset.prod_filter]; simp
  rw [Nat.card_divisors hn.ne', ← Finset.prod_pow]
  calc
    (∏ p ∈ n.primeFactors, (n.factorization p+1)^5) ≤
        ∏ p ∈ n.primeFactors, (if p < 32 then 512 else 1) * p^(n.factorization p) :=
      Finset.prod_le_prod' fun p hp => DivisorBound.prime_exponent p _
        (Nat.prime_of_mem_primeFactors hp)
    _ = 512 ^ (n.primeFactors.filter (· < 32)).card * n := by
      rw [Finset.prod_mul_distrib, hprod, ← Nat.prod_primeFactors_pow_factorization hn.ne']
    _ ≤ 512^32 * n := Nat.mul_le_mul_right n (Nat.pow_le_pow_right (by decide) hc)

end OPG37364


end Stage17BSource2

noncomputable section Stage17BSource3
-- Source: OPG37364.DivisorTenthBound
set_option autoImplicit false
open scoped BigOperators

namespace OPG37364.DivisorBound

theorem exponent_ten_large (e : ℕ) : (e+1)^10 ≤ 1024^e := by
  calc
    (e+1)^10 ≤ (2^e)^10 := Nat.pow_le_pow_left (Nat.succ_le_of_lt Nat.lt_two_pow_self) 10
    _ = 1024^e := by rw [← pow_mul, Nat.mul_comm e 10, pow_mul]; norm_num

theorem exponent_ten_small (e : ℕ) : (e+1)^10 ≤ 2^100 * 2^e := by
  induction e using Nat.strong_induction_on with
  | h e ih =>
    by_cases he : e ≤ 14
    · interval_cases e <;> norm_num
    · obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le (show 15 ≤ e by omega)
      have hprev := ih (14+k) (by omega)
      have hstep : (k+16)^10 ≤ 2*(k+15)^10 := by ring_nf; omega
      calc
        (15+k+1)^10 ≤ 2*(14+k+1)^10 := by
          simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hstep
        _ ≤ 2*(2^100*2^(14+k)) := Nat.mul_le_mul_left 2 hprev
        _ = 2^100*2^(15+k) := by
          rw [show 15+k=(14+k)+1 by omega, pow_succ]; ring

theorem prime_exponent_ten (p e : ℕ) (hp : p.Prime) :
    (e+1)^10 ≤ (if p < 1024 then 2^100 else 1) * p^e := by
  split_ifs with h
  · exact (exponent_ten_small e).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hp.two_le e))
  · simpa using (exponent_ten_large e).trans (Nat.pow_le_pow_left (by omega : 1024 ≤ p) e)

end OPG37364.DivisorBound

namespace OPG37364

theorem card_divisors_pow_ten_le (n : ℕ) (hn : 0 < n) :
    n.divisors.card ^ 10 ≤ (2^100)^1024 * n := by
  classical
  have hc : (n.primeFactors.filter (· < 1024)).card ≤ 1024 := by
    simpa using Finset.card_le_card (show n.primeFactors.filter (· < 1024) ⊆
      Finset.range 1024 from fun p hp => Finset.mem_range.mpr (Finset.mem_filter.mp hp).2)
  have hprod : (∏ p ∈ n.primeFactors, (if p < 1024 then 2^100 else 1 : ℕ)) =
      (2^100) ^ (n.primeFactors.filter (· < 1024)).card := by
    rw [← Finset.prod_filter]; simp
  rw [Nat.card_divisors hn.ne', ← Finset.prod_pow]
  calc
    (∏ p ∈ n.primeFactors, (n.factorization p+1)^10) ≤
        ∏ p ∈ n.primeFactors, (if p < 1024 then 2^100 else 1) * p^(n.factorization p) :=
      Finset.prod_le_prod' fun p hp => DivisorBound.prime_exponent_ten p _
        (Nat.prime_of_mem_primeFactors hp)
    _ = (2^100) ^ (n.primeFactors.filter (· < 1024)).card * n := by
      rw [Finset.prod_mul_distrib, hprod, ← Nat.prod_primeFactors_pow_factorization hn.ne']
    _ ≤ (2^100)^1024 * n := Nat.mul_le_mul_right n
      (Nat.pow_le_pow_right (by positivity) hc)

end OPG37364


end Stage17BSource3

noncomputable section Stage17BSource4
-- Source: OPG37364.SquareRepresentationBounds
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace OPG37364

theorem twoSquare_count_pow_five_le :
    ∃ D2 : ℕ, 0 < D2 ∧ ∀ N : ℕ, Stage17Probe.r2 N ^ 5 ≤ D2*(N+1) := by
  obtain ⟨D,hD,hdiv⟩ : ∃ D : ℕ, 0 < D ∧ ∀ n : ℕ, 0 < n →
      n.divisors.card^10 ≤ D*n :=
    ⟨(2^100)^1024, by positivity, card_divisors_pow_ten_le⟩
  refine ⟨9^5*D, by positivity, ?_⟩
  intro N
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · rw [Stage17Probe.r2_zero]
    simp only [one_pow, zero_add, mul_one]
    have hpos : 0 < (9 : ℕ)^5*D := by positivity
    omega
  · calc
      Stage17Probe.r2 N ^ 5 ≤ (9*N.divisors.card^2)^5 :=
        Nat.pow_le_pow_left (GaussianCount.twoSquare_count_le_nine_mul_divisors_sq N hN) 5
      _ = 9^5*N.divisors.card^10 := by ring
      _ ≤ 9^5*(D*N) := Nat.mul_le_mul_left _ (hdiv N hN)
      _ ≤ (9^5*D)*(N+1) := by
        rw [← mul_assoc]
        exact Nat.mul_le_mul_left _ (Nat.le_succ N)

end OPG37364

end

end Stage17BSource4

noncomputable section Stage17BSource5
-- Source: OPG37364.ThreeSquareCount
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace OPG37364.SquareCount

def signedRange (N : ℕ) : Finset ℤ := Finset.Icc (-(N.sqrt : ℤ)) N.sqrt

theorem mem_signedRange (N : ℕ) (z : ℤ) :
    z ∈ signedRange N ↔ z.natAbs^2 ≤ N := by
  rw [signedRange, Finset.mem_Icc, ← Nat.le_sqrt']
  omega

theorem signedRange_card (N : ℕ) : (signedRange N).card = 2*N.sqrt+1 := by
  rw [signedRange, Int.card_Icc]
  omega

def ThreeSquareData (N : ℕ) :=
  Σ z : {z // z ∈ signedRange N},
    {xy // xy ∈ Stage17Probe.twoSquarePairs (N-z.val.natAbs^2)}

instance (N : ℕ) : Fintype (ThreeSquareData N) :=
  @Sigma.instFintype {z // z ∈ signedRange N}
    (fun z => {xy // xy ∈ Stage17Probe.twoSquarePairs (N-z.val.natAbs^2)})
    (fun _ => inferInstance) inferInstance

def r3 (N : ℕ) : ℕ := Fintype.card (ThreeSquareData N)

theorem r3_eq_sum (N : ℕ) :
    r3 N = ∑ z ∈ signedRange N, Stage17Probe.r2 (N-z.natAbs^2) := by
  classical
  letI : ∀ z : {z // z ∈ signedRange N},
      Fintype {xy // xy ∈ Stage17Probe.twoSquarePairs (N-z.val.natAbs^2)} :=
    fun _ => inferInstance
  change Fintype.card (Σ z : {z // z ∈ signedRange N},
    {xy // xy ∈ Stage17Probe.twoSquarePairs (N-z.val.natAbs^2)}) = _
  rw [Fintype.card_sigma]
  simp only [Fintype.card_coe, Stage17Probe.r2, Finset.univ_eq_attach,
    Finset.sum_attach]
  exact Finset.sum_attach (signedRange N)
    (fun z => (Stage17Probe.twoSquarePairs (N-z.natAbs^2)).card)

def dataEquivTriples (N : ℕ) : ThreeSquareData N ≃
    {v : ℤ × (ℤ × ℤ) // v.1^2+v.2.1^2+v.2.2^2=(N : ℤ)} where
  toFun w := ⟨(w.1.val,w.2.val), by
    have hz := (mem_signedRange N w.1.val).mp w.1.property
    have hp := (Stage17Probe.mem_twoSquarePairs _ w.2.val).mp w.2.property
    rw [Nat.cast_sub hz] at hp
    simp only [Nat.cast_pow, Int.natCast_natAbs, sq_abs] at hp
    nlinarith⟩
  invFun v := by
    have hz : v.val.1.natAbs^2 ≤ N := by
      have h : v.val.1^2 ≤ (N : ℤ) := by
        nlinarith [v.property, sq_nonneg v.val.2.1, sq_nonneg v.val.2.2]
      exact_mod_cast (by simpa using h : (v.val.1.natAbs : ℤ)^2 ≤ (N : ℤ))
    refine ⟨⟨v.val.1,(mem_signedRange N _).mpr hz⟩, ⟨v.val.2, ?_⟩⟩
    apply (Stage17Probe.mem_twoSquarePairs _ _).mpr
    rw [Nat.cast_sub hz]
    simp only [Nat.cast_pow, Int.natCast_natAbs, sq_abs]
    nlinarith [v.property]
  left_inv w := by cases w; rfl
  right_inv v := by cases v; rfl

instance (N : ℕ) : Finite {v : ℤ × (ℤ × ℤ) // v.1^2+v.2.1^2+v.2.2^2=(N : ℤ)} :=
  Finite.of_equiv (ThreeSquareData N) (dataEquivTriples N)

theorem r3_eq_card_triples (N : ℕ) :
    r3 N = Nat.card {v : ℤ × (ℤ × ℤ) // v.1^2+v.2.1^2+v.2.2^2=(N : ℤ)} := by
  rw [← Nat.card_congr (dataEquivTriples N), Nat.card_eq_fintype_card]
  rfl

theorem threeSquare_count_pow_ten_le :
    ∃ D3 : ℕ, 0 < D3 ∧ ∀ N : ℕ, r3 N ^ 10 ≤ D3*(N+1)^7 := by
  obtain ⟨D2,hD2,h2⟩ := twoSquare_count_pow_five_le
  refine ⟨9^5*D2^2, by positivity, ?_⟩
  intro N
  let s := signedRange N
  let f : ℤ → ℕ := fun z => Stage17Probe.r2 (N-z.natAbs^2)
  let M := s.sup f
  have hs : s.Nonempty := ⟨0, (mem_signedRange N 0).mpr (by simp)⟩
  obtain ⟨z,hz,hM⟩ := Finset.exists_mem_eq_sup s hs f
  have hM5 : M^5 ≤ D2*(N+1) := by
    rw [show M=f z from hM]
    exact (h2 _).trans (Nat.mul_le_mul_left _ (by omega))
  have hM10 : M^10 ≤ D2^2*(N+1)^2 := by
    simpa [← pow_mul, mul_pow] using Nat.pow_le_pow_left hM5 2
  have hL : s.card^2 ≤ 9*(N+1) := by
    rw [show s.card=2*N.sqrt+1 from signedRange_card N]
    have hsq := Nat.sqrt_le' N
    nlinarith
  have hL10 : s.card^10 ≤ 9^5*(N+1)^5 := by
    simpa [← pow_mul, mul_pow] using Nat.pow_le_pow_left hL 5
  have hsum : r3 N ≤ s.card*M := by
    rw [r3_eq_sum]
    calc
      ∑ z ∈ signedRange N, f z ≤ ∑ _z ∈ s, M :=
        Finset.sum_le_sum fun z hz => Finset.le_sup (f := f) hz
      _ = s.card*M := by simp
  calc
    r3 N ^ 10 ≤ (s.card*M)^10 := Nat.pow_le_pow_left hsum 10
    _ = s.card^10*M^10 := mul_pow _ _ _
    _ ≤ (9^5*(N+1)^5)*(D2^2*(N+1)^2) := Nat.mul_le_mul hL10 hM10
    _ = (9^5*D2^2)*(N+1)^7 := by ring

end OPG37364.SquareCount

end

end Stage17BSource5

noncomputable section Stage17BSource6
-- Source: OPG37364.QuaternionCount
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace OPG37364.QuaternionCount

theorem square_congruence (q t : ℕ) (hq : q.Prime) (hq2 : 2 < q)
    (ht : ¬ q ∣ t) (a : ℤ) (ha : (q : ℤ)^2 ∣ (t : ℤ)^2-a^2) :
    (q : ℤ)^2 ∣ (t : ℤ)-a ∨ (q : ℤ)^2 ∣ (t : ℤ)+a := by
  have hp : Prime (q : ℤ) := (Int.prime_iff_natAbs_prime).mpr (by simpa using hq)
  have ht' : ¬ (q : ℤ) ∣ (t : ℤ) := by exact_mod_cast ht
  have htwo : ¬ (q : ℤ) ∣ 2 := by
    exact_mod_cast (Nat.not_dvd_of_pos_of_lt (by decide : 0 < 2) hq2)
  have hmul : (q : ℤ)^2 ∣ ((t : ℤ)-a)*((t : ℤ)+a) := by
    convert ha using 1 <;> ring
  by_cases hminus : (q : ℤ) ∣ (t : ℤ)-a
  · have hplus : ¬ (q : ℤ) ∣ (t : ℤ)+a := by
      intro h
      have hd : (q : ℤ) ∣ 2*(t : ℤ) := by
        have hh : (q : ℤ) ∣ ((t : ℤ)-a)+((t : ℤ)+a) := dvd_add hminus h
        rwa [show ((t : ℤ)-a)+((t : ℤ)+a)=2*(t : ℤ) by ring] at hh
      exact ht' ((hp.dvd_or_dvd hd).resolve_left htwo)
    exact Or.inl (hp.pow_dvd_of_dvd_mul_right 2 hplus hmul)
  · exact Or.inr (hp.pow_dvd_of_dvd_mul_left 2 hminus hmul)

/-- Shift the interval `[-t,t]` to `0,...,2*t`. -/
def admissibleOffsets (q t : ℕ) : Finset ℕ :=
  (Finset.range (2*t+1)).filter fun n =>
    (q : ℤ)^2 ∣ (t : ℤ)^2-((n : ℤ)-t)^2

theorem offset_remainder (q t n : ℕ) (hq : q.Prime) (hq2 : 2 < q)
    (ht : ¬ q ∣ t) (hn : n ∈ admissibleOffsets q t) :
    n % q^2 = 0 ∨ n % q^2 = (2*t) % q^2 := by
  have hd := (Finset.mem_filter.mp hn).2
  rcases square_congruence q t hq hq2 ht ((n : ℤ)-t) hd with h | h
  · right
    apply Nat.modEq_iff_dvd.mpr
    convert h using 1 <;> push_cast <;> ring
  · left
    apply Nat.mod_eq_zero_of_dvd
    have h' : (q : ℤ)^2 ∣ (n : ℤ) := by convert h using 1 <;> ring
    exact_mod_cast h'

theorem admissibleOffsets_card_le (q t : ℕ) (hq : q.Prime) (hq2 : 2 < q)
    (ht : ¬ q ∣ t) :
    (admissibleOffsets q t).card ≤ 2*((2*t)/q^2+1) := by
  classical
  let target := ({0, (2*t)%q^2} : Finset ℕ).product
    (Finset.range ((2*t)/q^2+1))
  have hcard : (admissibleOffsets q t).card ≤ target.card := by
    apply Finset.card_le_card_of_injOn (fun n => (n%q^2,n/q^2))
    · intro n hn
      apply Finset.mem_product.mpr
      constructor
      · simpa only [Finset.mem_insert, Finset.mem_singleton] using
          offset_remainder q t n hq hq2 ht hn
      · apply Finset.mem_range.mpr
        change n/q^2 < (2*t)/q^2+1
        have hn' : n ≤ 2*t := by
          have := Finset.mem_range.mp (Finset.mem_filter.mp hn).1
          omega
        have := Nat.div_le_div_right (c := q^2) hn'
        omega
    · intro n hn m hm he
      have hr := congrArg Prod.fst he
      have hd := congrArg Prod.snd he
      have hne := Nat.mod_add_div n (q^2)
      have hme := Nat.mod_add_div m (q^2)
      simp only [Prod.fst, Prod.snd] at hr hd
      calc
        n = n%q^2 + q^2*(n/q^2) := hne.symm
        _ = m%q^2 + q^2*(m/q^2) := by rw [hr,hd]
        _ = m := hme
  apply hcard.trans
  dsimp [target]
  rw [Finset.card_product, Finset.card_range]
  exact Nat.mul_le_mul_right _ (by
    calc
      ({0,(2*t)%q^2} : Finset ℕ).card ≤ 1+({(2*t)%q^2} : Finset ℕ).card :=
        (Finset.card_insert_le _ _).trans_eq (by omega)
      _ = 2 := by simp)

def residual (q t n : ℕ) : ℕ :=
  (((t : ℤ)^2-((n : ℤ)-t)^2).toNat)/q^2

def Rq (q t : ℕ) : ℕ :=
  ∑ n ∈ admissibleOffsets q t, SquareCount.r3 (residual q t n)

theorem residual_mul_le (q t n : ℕ) : q^2 * residual q t n ≤ t^2 := by
  apply (Nat.mul_div_le _ _).trans
  have h : (t : ℤ)^2-((n : ℤ)-t)^2 ≤ (t : ℤ)^2 := by
    nlinarith [sq_nonneg ((n : ℤ)-t)]
  exact_mod_cast Int.toNat_le_toNat h

theorem residual_succ_mul_le (q t n : ℕ) (hqt : q ≤ t) :
    q^2 * (residual q t n+1) ≤ 2*t^2 := by
  have h := residual_mul_le q t n
  have hs := Nat.pow_le_pow_left hqt 2
  nlinarith

theorem quaternion_count_pow_ten_le :
    ∃ Dq : ℕ, 0 < Dq ∧ ∀ q t : ℕ, q.Prime → 2 < q → ¬q∣t → q ≤ t →
      Rq q t ^ 10 * q^34 ≤ Dq*(t^24+t^14*q^20) := by
  obtain ⟨D3,hD3,h3⟩ := SquareCount.threeSquare_count_pow_ten_le
  refine ⟨6^10*(D3*2^7), by positivity, ?_⟩
  intro q t hp hq ht hqt
  classical
  let s := admissibleOffsets q t
  let f := fun n => SquareCount.r3 (residual q t n)
  let M := s.sup f
  have hM : M^10*q^14 ≤ D3*2^7*t^14 := by
    by_cases hs : s.Nonempty
    · obtain ⟨n,hn,hMn⟩ := Finset.exists_mem_eq_sup s hs f
      rw [show M=f n from hMn]
      calc
        f n^10*q^14 ≤ (D3*(residual q t n+1)^7)*q^14 :=
          Nat.mul_le_mul_right _ (h3 _)
        _ = D3*(q^2*(residual q t n+1))^7 := by ring
        _ ≤ D3*(2*t^2)^7 := Nat.mul_le_mul_left _
          (Nat.pow_le_pow_left (residual_succ_mul_le q t n hqt) 7)
        _ = D3*2^7*t^14 := by ring
    · have hs' := Finset.not_nonempty_iff_eq_empty.mp hs
      simp [M,hs']
  have hsum : Rq q t ≤ s.card*M := by
    apply (Finset.sum_le_sum fun n hn => Finset.le_sup (f := f) hn).trans_eq
    simp [s,M]
  have hL := admissibleOffsets_card_le q t hp hq ht
  change s.card ≤ 2*((2*t)/q^2+1) at hL
  have hpow : Rq q t^10 ≤ s.card^10*M^10 := by
    simpa [mul_pow] using Nat.pow_le_pow_left hsum 10
  by_cases hsmall : t ≤ q^2
  · have hdiv : (2*t)/q^2 ≤ 2 := by
      apply (Nat.div_le_div_right (c := q^2) (Nat.mul_le_mul_left 2 hsmall)).trans
      exact le_of_eq (Nat.mul_div_cancel 2 (show 0 < q^2 by positivity))
    have hL6 : s.card ≤ 6 := by omega
    calc
      Rq q t^10*q^34 ≤ (s.card^10*M^10)*q^34 := Nat.mul_le_mul_right _ hpow
      _ = s.card^10*(M^10*q^14)*q^20 := by ring
      _ ≤ 6^10*(D3*2^7*t^14)*q^20 :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.pow_le_pow_left hL6 10) hM)
      _ = (6^10*(D3*2^7))*(t^14*q^20) := by ring
      _ ≤ (6^10*(D3*2^7))*(t^24+t^14*q^20) :=
        Nat.mul_le_mul_left _ (Nat.le_add_left _ _)
  · have hlarge : q^2 ≤ t := by omega
    have hdiv := Nat.div_mul_le_self (2*t) (q^2)
    have hLq : s.card*q^2 ≤ 6*t := by
      have hh := Nat.mul_le_mul_right (q^2) hL
      nlinarith
    calc
      Rq q t^10*q^34 ≤ (s.card^10*M^10)*q^34 := Nat.mul_le_mul_right _ hpow
      _ = (s.card*q^2)^10*(M^10*q^14) := by ring
      _ ≤ (6*t)^10*(D3*2^7*t^14) :=
        Nat.mul_le_mul (Nat.pow_le_pow_left hLq 10) hM
      _ = (6^10*(D3*2^7))*t^24 := by ring
      _ ≤ (6^10*(D3*2^7))*(t^24+t^14*q^20) :=
        Nat.mul_le_mul_left _ (Nat.le_add_right _ _)

end OPG37364.QuaternionCount

end

end Stage17BSource6

noncomputable section Stage17BSource7
-- Source: OPG37364.QuaternionCountFiber
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace OPG37364.QuaternionCount

def Quadruples (q t : ℕ) :=
  {v : ℤ × (ℤ × (ℤ × ℤ)) //
    v.1^2+(q : ℤ)^2*(v.2.1^2+v.2.2.1^2+v.2.2.2^2)=(t : ℤ)^2}

def CountData (q t : ℕ) :=
  Σ n : {n // n ∈ admissibleOffsets q t}, SquareCount.ThreeSquareData (residual q t n.val)

instance (q t : ℕ) : Fintype (CountData q t) :=
  @Sigma.instFintype {n // n ∈ admissibleOffsets q t}
    (fun n => SquareCount.ThreeSquareData (residual q t n.val))
    (fun _ => inferInstance) inferInstance

theorem countData_card (q t : ℕ) : Fintype.card (CountData q t) = Rq q t := by
  classical
  letI : ∀ n : {n // n ∈ admissibleOffsets q t},
      Fintype (SquareCount.ThreeSquareData (residual q t n.val)) := fun _ => inferInstance
  change Fintype.card (Σ n : {n // n ∈ admissibleOffsets q t},
    SquareCount.ThreeSquareData (residual q t n.val)) = _
  rw [Fintype.card_sigma]
  simp only [Finset.univ_eq_attach, Rq, SquareCount.r3]
  exact Finset.sum_attach (admissibleOffsets q t)
    (fun n => Fintype.card (SquareCount.ThreeSquareData (residual q t n)))

theorem quad_abs_le (q t : ℕ) (v : Quadruples q t) :
    -(t : ℤ) ≤ v.val.1 ∧ v.val.1 ≤ t := by
  have hs : 0 ≤ v.val.2.1^2+v.val.2.2.1^2+v.val.2.2.2^2 := by positivity
  have hprod := mul_nonneg (sq_nonneg (q : ℤ)) hs
  have he := v.property
  constructor <;> nlinarith

def quadOffset (q t : ℕ) (v : Quadruples q t) : {n // n ∈ admissibleOffsets q t} :=
  ⟨(v.val.1+t).toNat, by
    have hv := quad_abs_le q t v
    have he : (((v.val.1+t).toNat : ℕ) : ℤ)=v.val.1+t := Int.toNat_of_nonneg (by omega)
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_range.mpr
      omega
    · refine ⟨v.val.2.1^2+v.val.2.2.1^2+v.val.2.2.2^2, ?_⟩
      rw [he]
      nlinarith [v.property]⟩

theorem quad_residual (q t : ℕ) (hq : 0 < q) (v : Quadruples q t) :
    (residual q t (quadOffset q t v).val : ℤ) =
      v.val.2.1^2+v.val.2.2.1^2+v.val.2.2.2^2 := by
  have hv := quad_abs_le q t v
  have he : (((v.val.1+t).toNat : ℕ) : ℤ)=v.val.1+t := Int.toNat_of_nonneg (by omega)
  let N := v.val.2.1.natAbs^2+v.val.2.2.1.natAbs^2+v.val.2.2.2.natAbs^2
  have hN : (N : ℤ)=v.val.2.1^2+v.val.2.2.1^2+v.val.2.2.2^2 := by
    simp [N]
  have hnum : (t : ℤ)^2-(((quadOffset q t v).val : ℤ)-t)^2 = (q^2*N : ℕ) := by
    dsimp [quadOffset]
    rw [he]
    push_cast
    rw [hN]
    nlinarith [v.property]
  simp only [residual, hnum, Int.toNat_natCast]
  rw [Nat.mul_div_right _ (show 0 < q^2 by positivity)]
  exact hN

def quadToData (q t : ℕ) (hq : 0 < q) (v : Quadruples q t) : CountData q t :=
  ⟨quadOffset q t v, (SquareCount.dataEquivTriples _).symm
    ⟨v.val.2, (quad_residual q t hq v).symm⟩⟩

theorem quadToData_injective (q t : ℕ) (hq : 0 < q) :
    Function.Injective (quadToData q t hq) := by
  intro v w he
  have hfirst := congrArg (fun d : CountData q t => d.1.val) he
  have hsecond := congrArg (fun d : CountData q t =>
    ((SquareCount.dataEquivTriples _ d.2).val : ℤ × (ℤ × ℤ))) he
  simp only [quadToData, Equiv.apply_symm_apply] at hsecond
  have hv := quad_abs_le q t v
  have hw := quad_abs_le q t w
  have hval : v.val.1 = w.val.1 := by
    change (v.val.1+t).toNat=(w.val.1+t).toNat at hfirst
    omega
  apply Subtype.ext
  exact Prod.ext hval hsecond

instance (q t : ℕ) [hq : Fact (0 < q)] : Finite (Quadruples q t) :=
  Finite.of_injective (quadToData q t hq.out) (quadToData_injective q t hq.out)

theorem card_quadruples_le_Rq (q t : ℕ) (hq : 0 < q) :
    Nat.card (Quadruples q t) ≤ Rq q t := by
  have h := Nat.card_le_card_of_injective (quadToData q t hq) (quadToData_injective q t hq)
  simpa [Nat.card_eq_fintype_card, countData_card] using h

end OPG37364.QuaternionCount

end

end Stage17BSource7

noncomputable section Stage17BSource8
-- Source: Theorems.Thm_OPG37364_lps13_reduced_word_not_all_coords_dvd13
set_option autoImplicit false

namespace OPG37364
namespace WordPrimitivity

abbrev F := ZMod 13
abbrev Mat := Matrix (Fin 2) (Fin 2) F
local instance : Fact (Nat.Prime 13) := ⟨by decide⟩

/-- Auxiliary full matrix ring at the fixed modulus 13; no GL/PGL construction. -/
def theta (x : Quaternion ℤ) : Mat := lps13QuaternionMatrix (q := 13) 5 x

theorem five_sq : (5 : F) ^ 2 = -1 := by decide

theorem theta_one : theta 1 = 1 := by
  ext j k
  fin_cases j <;> fin_cases k <;> decide

theorem theta_mul (x y : Quaternion ℤ) : theta (x * y) = theta x * theta y := by
  have h25 : (25 : F) = -1 := by decide
  ext j k
  fin_cases j <;> fin_cases k <;>
    simp [theta, lps13QuaternionMatrix, Quaternion.re_mul, Quaternion.imI_mul,
      Quaternion.imJ_mul, Quaternion.imK_mul, Matrix.mul_apply, Fin.sum_univ_two] <;>
    ring_nf <;> rw [h25] <;> ring

theorem theta_zero_of_dvd (x : Quaternion ℤ)
    (h : (13 : ℤ) ∣ x.re ∧ 13 ∣ x.imI ∧ 13 ∣ x.imJ ∧ 13 ∣ x.imK) : theta x = 0 := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  have h0' := (ZMod.intCast_zmod_eq_zero_iff_dvd x.re 13).mpr h0
  have h1' := (ZMod.intCast_zmod_eq_zero_iff_dvd x.imI 13).mpr h1
  have h2' := (ZMod.intCast_zmod_eq_zero_iff_dvd x.imJ 13).mpr h2
  have h3' := (ZMod.intCast_zmod_eq_zero_iff_dvd x.imK 13).mpr h3
  ext j k
  fin_cases j <;> fin_cases k <;>
    simp [theta, lps13QuaternionMatrix, h0', h1', h2', h3']

def U : Fin 14 → Fin 2 → F :=
  ![![11,8], ![11,1], ![11,12], ![11,5],
    ![4,8], ![4,1], ![4,12], ![4,5],
    ![0,6], ![6,0], ![3,11], ![3,2], ![3,10], ![3,3]]

def V : Fin 14 → Fin 2 → F :=
  ![![1,7], ![1,4], ![1,9], ![1,6],
    ![1,3], ![1,11], ![1,2], ![1,10],
    ![0,1], ![1,0], ![1,5], ![1,8], ![1,12], ![1,1]]

def outer (u v : Fin 2 → F) : Mat := fun j k => u j * v k
def pairing (a b : Fin 14) : F := (V a 0 * U b 0) + (V a 1 * U b 1)

theorem factors_nonzero : ∀ a : Fin 14, U a ≠ 0 ∧ V a ≠ 0 := by decide

theorem generator_factor : ∀ a : Fin 14,
    theta (lps13Quaternion a) = outer (U a) (V a) := by decide

theorem pairing_zero_iff : ∀ a b : Fin 14,
    pairing a b = 0 ↔ b = lps13ConjIndex a := by decide

theorem outer_mul (u v u' v' : Fin 2 → F) :
    outer u v * outer u' v' = (v 0 * u' 0 + v 1 * u' 1) • outer u v' := by
  ext j k
  simp [outer, Matrix.mul_apply, Fin.sum_univ_two, smul_eq_mul]
  ring

theorem smul_outer_ne_zero {t : F} (ht : t ≠ 0) {u v : Fin 2 → F}
    (hu : u ≠ 0) (hv : v ≠ 0) : t • outer u v ≠ 0 := by
  obtain ⟨j, hj⟩ : ∃ j, u j ≠ 0 := by
    by_contra h
    push Not at h
    exact hu (funext h)
  obtain ⟨k, hk⟩ : ∃ k, v k ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (funext h)
  intro h
  have he := congrArg (fun M : Mat => M j k) h
  exact (mul_ne_zero ht (mul_ne_zero hj hk)) (by simpa [outer, smul_eq_mul] using he)

/-- Symbolic invariant for every length: first/last outer factors and nonzero coefficient. -/
theorem word_factor (a : Fin 14) (w : List (Fin 14)) (h : lps13WordReduced (a :: w)) :
    ∃ (z : Fin 14) (t : F), (a :: w).getLast? = some z ∧ t ≠ 0 ∧
      theta (lps13WordProduct (a :: w)) = t • outer (U a) (V z) := by
  induction w generalizing a with
  | nil =>
    refine ⟨a, 1, by simp, (one_ne_zero : (1 : F) ≠ 0), ?_⟩
    simpa [lps13WordProduct] using generator_factor a
  | cons b w ih =>
    obtain ⟨hab, hw⟩ := h
    obtain ⟨z, t, hz, ht, he⟩ := ih b hw
    have hc : pairing a b ≠ 0 := (pairing_zero_iff a b).not.mpr hab
    refine ⟨z, t * pairing a b, ?_, mul_ne_zero ht hc, ?_⟩
    · simpa using hz
    · calc
        theta (lps13WordProduct (a :: b :: w)) =
            theta (lps13Quaternion a) * theta (lps13WordProduct (b :: w)) := by
          simp only [lps13WordProduct, List.map_cons, List.prod_cons, theta_mul]
        _ = outer (U a) (V a) * (t • outer (U b) (V z)) := by rw [generator_factor, he]
        _ = (t * pairing a b) • outer (U a) (V z) := by
          rw [Matrix.mul_smul, outer_mul, smul_smul]
          rfl

theorem theta_word_ne_zero (w : List (Fin 14)) (h : lps13WordReduced w) :
    theta (lps13WordProduct w) ≠ 0 := by
  cases w with
  | nil => simpa [lps13WordProduct, theta_one] using (one_ne_zero : (1 : Mat) ≠ 0)
  | cons a w =>
    obtain ⟨z, t, _, ht, he⟩ := word_factor a w h
    rw [he]
    exact smul_outer_ne_zero ht (factors_nonzero a).1 (factors_nonzero z).2

end WordPrimitivity

/-- Every reduced word is 13-primitive: its four coordinates are not all divisible by 13. -/
theorem lps13_reduced_word_not_all_coords_dvd13
    (w : List (Fin 14)) (h : lps13WordReduced w) :
    ¬ ((13 : ℤ) ∣ (lps13WordProduct w).re ∧
      13 ∣ (lps13WordProduct w).imI ∧ 13 ∣ (lps13WordProduct w).imJ ∧
      13 ∣ (lps13WordProduct w).imK) := by
  intro hd
  exact WordPrimitivity.theta_word_ne_zero w h (WordPrimitivity.theta_zero_of_dvd _ hd)

end OPG37364


end Stage17BSource8

noncomputable section Stage17BSource9
-- Source: OPG37364.LPS13ScaledWordInjectivity
set_option autoImplicit false

namespace OPG37364
namespace ScaledWordInjectivity

-- These two structural identities are reused from Stage 7, LPS13Graph.lean.
theorem conj_involutive : Function.Involutive lps13ConjIndex := by
  change ∀ a, lps13ConjIndex (lps13ConjIndex a) = a
  decide

theorem quaternion_conj (a : Fin 14) :
    lps13Quaternion (lps13ConjIndex a) = star (lps13Quaternion a) := by
  fin_cases a <;> rfl

theorem generator_mul_conj (a : Fin 14) :
    lps13Quaternion a * lps13Quaternion (lps13ConjIndex a) =
      (13 : ℤ) • (1 : Quaternion ℤ) := by
  rw [quaternion_conj, Quaternion.self_mul_star, lps13Quaternion_norm]
  rfl

-- The norm induction is reused from Stage 11, LPS13WordPrimitivity.lean.
theorem word_norm (w : List (Fin 14)) :
    Quaternion.normSq (lps13WordProduct w) = (13 : ℤ) ^ w.length := by
  induction w with
  | nil => simp [lps13WordProduct]
  | cons a w ih =>
    simpa [lps13WordProduct, map_mul, lps13Quaternion_norm, pow_succ, mul_comm] using
      congrArg (fun z : ℤ => 13 * z) ih

-- This interface to List.IsChain is reused from Stage 12, LPS13CycleWords.lean.
theorem reduced_iff_chain (w : List (Fin 14)) :
    lps13WordReduced w ↔ w.IsChain (fun a b => b ≠ lps13ConjIndex a) := by
  induction w with
  | nil => simp [lps13WordReduced]
  | cons a w ih =>
    cases w with
    | nil => simp [lps13WordReduced]
    | cons b w =>
      simpa only [lps13WordReduced, List.isChain_cons_cons] using and_congr Iff.rfl ih

theorem product_append (u v : List (Fin 14)) :
    lps13WordProduct (u ++ v) = lps13WordProduct u * lps13WordProduct v := by
  simp [lps13WordProduct]

theorem product_snoc (u : List (Fin 14)) (a : Fin 14) :
    lps13WordProduct (u ++ [a]) = lps13WordProduct u * lps13Quaternion a := by
  simp [lps13WordProduct]

theorem scalar_cancel {c : ℤ} (hc : c ≠ 0) {x y : Quaternion ℤ}
    (h : c • x = c • y) : x = y := by
  apply Quaternion.ext
  · exact mul_left_cancel₀ hc (congrArg (fun z : Quaternion ℤ => z.re) h)
  · exact mul_left_cancel₀ hc (congrArg (fun z : Quaternion ℤ => z.imI) h)
  · exact mul_left_cancel₀ hc (congrArg (fun z : Quaternion ℤ => z.imJ) h)
  · exact mul_left_cancel₀ hc (congrArg (fun z : Quaternion ℤ => z.imK) h)

theorem primitive_not_thirteen_smul (w : List (Fin 14)) (hw : lps13WordReduced w)
    (x : Quaternion ℤ) : lps13WordProduct w ≠ (13 : ℤ) • x := by
  intro h
  apply lps13_reduced_word_not_all_coords_dvd13 w hw
  rw [h]
  exact ⟨⟨x.re, rfl⟩, ⟨x.imI, rfl⟩, ⟨x.imJ, rfl⟩, ⟨x.imK, rfl⟩⟩

theorem product_snoc_mul_conj (u : List (Fin 14)) (a : Fin 14) :
    lps13WordProduct (u ++ [a]) * lps13Quaternion (lps13ConjIndex a) =
      (13 : ℤ) • lps13WordProduct u := by
  rw [product_snoc, mul_assoc, generator_mul_conj, mul_smul_comm, mul_one]

theorem reduced_prefix (u : List (Fin 14)) (a : Fin 14)
    (h : lps13WordReduced (u ++ [a])) : lps13WordReduced u :=
  (reduced_iff_chain u).2 ((reduced_iff_chain _).1 h).left_of_append

theorem reduced_extend (v : List (Fin 14)) (a b : Fin 14)
    (hv : lps13WordReduced (v ++ [b])) (hab : a ≠ b) :
    lps13WordReduced ((v ++ [b]) ++ [lps13ConjIndex a]) := by
  apply (reduced_iff_chain _).2
  apply ((reduced_iff_chain _).1 hv).append (by simp)
  simpa using fun (h : lps13ConjIndex a = lps13ConjIndex b) =>
    hab (conj_involutive.injective h)

theorem product_injective_of_length (u v : List (Fin 14))
    (hu : lps13WordReduced u) (hv : lps13WordReduced v)
    (hlen : u.length = v.length) (hprod : lps13WordProduct u = lps13WordProduct v) :
    u = v := by
  induction u using List.reverseRecOn generalizing v with
  | nil => exact (List.length_eq_zero_iff.mp hlen.symm).symm
  | append_singleton u a ih =>
    have hvne : v ≠ [] := by intro h; simp [h] at hlen
    obtain ⟨v, b, rfl⟩ : ∃ t b, v = t ++ [b] :=
      ⟨v.dropLast, v.getLast hvne, (List.dropLast_concat_getLast hvne).symm⟩
    have hab : a = b := by
      by_contra hab
      apply primitive_not_thirteen_smul _ (reduced_extend v a b hv hab) (lps13WordProduct u)
      rw [product_snoc, ← hprod, product_snoc_mul_conj]
    subst b
    have hpref : lps13WordProduct u = lps13WordProduct v := by
      apply scalar_cancel (by norm_num : (13 : ℤ) ≠ 0)
      simpa only [product_snoc_mul_conj] using
        congrArg (fun x => x * lps13Quaternion (lps13ConjIndex a)) hprod
    have huv := ih v (reduced_prefix u a hu) (reduced_prefix v a hv)
      (by simpa using hlen) hpref
    rw [huv]

theorem exponent_not_lt (r s : ℕ) (u v : List (Fin 14))
    (hu : lps13WordReduced u)
    (h : (13 : ℤ)^r • lps13WordProduct u = (13 : ℤ)^s • lps13WordProduct v) :
    ¬ r < s := by
  intro hrs
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hrs)
  have hs : s = r + (d + 1) := by omega
  have he : lps13WordProduct u = (13 : ℤ) • ((13 : ℤ)^d • lps13WordProduct v) := by
    apply scalar_cancel (pow_ne_zero r (by norm_num : (13 : ℤ) ≠ 0))
    simpa only [hs, pow_add, pow_succ', mul_smul] using h
  exact primitive_not_thirteen_smul u hu _ he

end ScaledWordInjectivity

/-- Literal integral quaternion equality determines both the power of 13 and the reduced word. -/
theorem lps13_scaled_reduced_word_product_injective
    (r s : ℕ) (u v : List (Fin 14))
    (hu : lps13WordReduced u) (hv : lps13WordReduced v)
    (h : (13 : ℤ)^r • lps13WordProduct u = (13 : ℤ)^s • lps13WordProduct v) :
    r = s ∧ u = v := by
  have hrs : r = s := by
    have h₁ := ScaledWordInjectivity.exponent_not_lt r s u v hu h
    have h₂ := ScaledWordInjectivity.exponent_not_lt s r v u hv h.symm
    omega
  subst s
  have hp := ScaledWordInjectivity.scalar_cancel
    (pow_ne_zero r (by norm_num : (13 : ℤ) ≠ 0)) h
  have hn := congrArg Quaternion.normSq hp
  rw [ScaledWordInjectivity.word_norm, ScaledWordInjectivity.word_norm] at hn
  have hl := (pow_right_strictMono₀ (by norm_num : (1 : ℤ) < 13)).injective hn
  exact ⟨rfl, ScaledWordInjectivity.product_injective_of_length u v hu hv hl hp⟩

end OPG37364


end Stage17BSource9

noncomputable section Stage17BSource10
-- Source: OPG37364.LPS13Graph
set_option autoImplicit false
open scoped Quaternion

namespace OPG37364

theorem lps13Coords_injective : Function.Injective lps13Coords := by
  decide

theorem lps13Coords_bounds (a : Fin 14) (k : Fin 4) :
    -3 ≤ lps13Coords a k ∧ lps13Coords a k ≤ 3 := by
  revert a k
  decide

theorem lps13Coords_re_pos (a : Fin 14) : 0 < lps13Coords a 0 := by
  revert a
  decide

theorem lps13Coords_im_nonzero (a : Fin 14) :
    ∃ k : Fin 4, k ≠ 0 ∧ lps13Coords a k ≠ 0 := by
  revert a
  decide

theorem lps13ConjIndex_involutive : Function.Involutive lps13ConjIndex := by
  change ∀ a, lps13ConjIndex (lps13ConjIndex a) = a
  decide

theorem lps13Quaternion_conj (a : Fin 14) :
    lps13Quaternion (lps13ConjIndex a) = star (lps13Quaternion a) := by
  fin_cases a <;> rfl

theorem lps13Quaternion_injective : Function.Injective lps13Quaternion := by
  intro a b h
  apply lps13Coords_injective
  funext k
  fin_cases k
  · exact congrArg QuaternionAlgebra.re h
  · exact congrArg QuaternionAlgebra.imI h
  · exact congrArg QuaternionAlgebra.imJ h
  · exact congrArg QuaternionAlgebra.imK h

theorem lps13Root_nonempty {q : ℕ} [Fact q.Prime] (h4 : q % 4 = 1) :
    Nonempty (LPS13Root q) := by
  obtain ⟨i, hi⟩ := (isSquare_iff_exists_sq (-1 : ZMod q)).mp
    (ZMod.exists_sq_eq_neg_one_iff.mpr (by omega : q % 4 ≠ 3))
  exact ⟨⟨i, hi.symm⟩⟩

section FiniteField

variable {q : ℕ} [Fact q.Prime] (hq : 13 < q) (i : LPS13Root q)

include hq in
private theorem small_intCast_inj {x y : ℤ}
    (hx : -3 ≤ x ∧ x ≤ 3) (hy : -3 ≤ y ∧ y ≤ 3)
    (h : (x : ZMod q) = y) : x = y := by
  have hq' : (13 : ℤ) < q := by exact_mod_cast hq
  have he : x + 3 = y + 3 :=
    CharP.intCast_injOn_Ico (ZMod q) q
      (by constructor <;> omega) (by constructor <;> omega)
      (by push_cast; rw [h])
  omega

include hq in
private theorem two_ne_zero : (2 : ZMod q) ≠ 0 := by
  simpa using (ZMod.natCast_eq_zero_iff 2 q).not.mpr
    (Nat.not_dvd_of_pos_of_lt (by decide) (by omega))

private theorem root_ne_zero : i.val ≠ 0 := by
  intro h
  have hi := i.property
  rw [h] at hi
  simp at hi

include hq in
private theorem matrix_coordinates (a b : Quaternion ℤ) (r : ZMod q)
    (h : lps13QuaternionMatrix i.val a = r • lps13QuaternionMatrix i.val b) :
    (a.re : ZMod q) = r * b.re ∧ (a.imI : ZMod q) = r * b.imI ∧
    (a.imJ : ZMod q) = r * b.imJ ∧ (a.imK : ZMod q) = r * b.imK := by
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) (ZMod q) => M 0 0) h
  have h11 := congrArg (fun M : Matrix (Fin 2) (Fin 2) (ZMod q) => M 1 1) h
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) (ZMod q) => M 0 1) h
  have h10 := congrArg (fun M : Matrix (Fin 2) (Fin 2) (ZMod q) => M 1 0) h
  simp [lps13QuaternionMatrix, Matrix.smul_apply, smul_eq_mul] at h00 h11 h01 h10
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply mul_left_cancel₀ (two_ne_zero hq)
    linear_combination h00 + h11
  · apply mul_left_cancel₀ (mul_ne_zero (two_ne_zero hq) (root_ne_zero i))
    linear_combination h00 - h11
  · apply mul_left_cancel₀ (two_ne_zero hq)
    linear_combination h01 - h10
  · apply mul_left_cancel₀ (mul_ne_zero (two_ne_zero hq) (root_ne_zero i))
    linear_combination h01 + h10

include hq in
private theorem indexed_matrix_coordinates (a b : Fin 14) (r : ZMod q)
    (h : lps13Matrix i a = r • lps13Matrix i b) :
    ∀ k : Fin 4, (lps13Coords a k : ZMod q) = r * lps13Coords b k := by
  obtain ⟨h0, h1, h2, h3⟩ := matrix_coordinates hq i (lps13Quaternion a)
    (lps13Quaternion b) r h
  intro k
  fin_cases k
  · exact h0
  · exact h1
  · exact h2
  · exact h3

theorem lps13Matrix_det (a : Fin 14) : (lps13Matrix i a).det = 13 := by
  simp [lps13Matrix, lps13QuaternionMatrix_det, lps13Quaternion_norm]

private theorem projective_scalar (a b : Fin 14)
    (h : lps13Generator hq i a = lps13Generator hq i b) :
    ∃ r : (ZMod q)ˣ, lps13Matrix i b = (r : ZMod q) • lps13Matrix i a := by
  obtain ⟨r, hr⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp h
  refine ⟨r, ?_⟩
  have hm := congrArg Units.val hr
  ext j k
  have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) (ZMod q) => M j k) hm
  simpa [lps13GL, Matrix.GeneralLinearGroup.val_mkOfDetNeZero,
    Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar, Matrix.mul_diagonal,
    Matrix.smul_apply, smul_eq_mul, mul_comm] using he.symm

theorem lps13Generator_injective : Function.Injective (lps13Generator hq i) := by
  intro a b hab
  obtain ⟨r, hr⟩ := projective_scalar hq i a b hab
  have hd := congrArg Matrix.det hr
  rw [Matrix.det_smul, lps13Matrix_det, lps13Matrix_det] at hd
  have h13 : (13 : ZMod q) ≠ 0 := by
    simpa using (ZMod.natCast_eq_zero_iff 13 q).not.mpr
      (Nat.not_dvd_of_pos_of_lt (by decide) hq)
  have hs : (r : ZMod q) ^ 2 = 1 := by
    apply mul_right_cancel₀ h13
    simpa using hd.symm
  obtain hr1 | hrn := sq_eq_one_iff.mp hs
  · apply lps13Coords_injective
    funext k
    have hk := indexed_matrix_coordinates hq i b a r hr k
    rw [hr1, one_mul] at hk
    exact (small_intCast_inj hq (lps13Coords_bounds b k) (lps13Coords_bounds a k) hk).symm
  · have hk := indexed_matrix_coordinates hq i b a r hr 0
    rw [hrn, neg_one_mul] at hk
    have he : lps13Coords b 0 = -lps13Coords a 0 :=
      small_intCast_inj hq (lps13Coords_bounds b 0)
        (by have hb := lps13Coords_bounds a 0; constructor <;> omega)
        (by simpa using hk)
    have ha := lps13Coords_re_pos a
    have hb := lps13Coords_re_pos b
    omega

theorem lps13Generator_ne_one (a : Fin 14) : lps13Generator hq i a ≠ 1 := by
  intro h
  have h' : Matrix.ProjGenLinGroup.mk (lps13GL hq i a) =
      Matrix.ProjGenLinGroup.mk (1 : Matrix.GeneralLinearGroup (Fin 2) (ZMod q)) := h
  obtain ⟨r, hr⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp h'.symm
  have hm : lps13Matrix i a = (r : ZMod q) • lps13QuaternionMatrix i.val (1 : Quaternion ℤ) := by
    have he := congrArg Units.val hr
    ext j k
    have he' := (congrArg (fun M : Matrix (Fin 2) (Fin 2) (ZMod q) => M j k) he).symm
    fin_cases j <;> fin_cases k <;>
      simpa [lps13GL, lps13QuaternionMatrix, Matrix.GeneralLinearGroup.coe_scalar,
        Matrix.scalar, Matrix.diagonal] using he'
  obtain ⟨_, h1, h2, h3⟩ := matrix_coordinates hq i (lps13Quaternion a) 1 r hm
  have him : ∀ k : Fin 4, k ≠ 0 → (lps13Coords a k : ZMod q) = 0 := by
    intro k hk
    fin_cases k
    · exact (hk rfl).elim
    · simpa [lps13Quaternion] using h1
    · simpa [lps13Quaternion] using h2
    · simpa [lps13Quaternion] using h3
  obtain ⟨k, hk, hn⟩ := lps13Coords_im_nonzero a
  exact hn (small_intCast_inj hq (lps13Coords_bounds a k) (by norm_num)
    (by simpa using him k hk))

private theorem quaternionMatrix_mul_star (a : Quaternion ℤ) :
    lps13QuaternionMatrix i.val a * lps13QuaternionMatrix i.val (star a) =
      (((Quaternion.normSq a : ℤ) : ZMod q)) • (1 : Matrix (Fin 2) (Fin 2) (ZMod q)) := by
  ext j k
  fin_cases j <;> fin_cases k <;>
    simp [lps13QuaternionMatrix, Matrix.mul_apply, Fin.sum_univ_two,
      Quaternion.normSq_def'] <;>
    first | ring1 | linear_combination -(a.imI : ZMod q)^2 * i.property -
      (a.imK : ZMod q)^2 * i.property

theorem lps13Matrix_mul_conj (a : Fin 14) :
    lps13Matrix i a * lps13Matrix i (lps13ConjIndex a) =
      (13 : ZMod q) • (1 : Matrix (Fin 2) (Fin 2) (ZMod q)) := by
  simpa [lps13Matrix, lps13Quaternion_conj, lps13Quaternion_norm] using
    quaternionMatrix_mul_star i (lps13Quaternion a)

theorem lps13Generator_conj (a : Fin 14) :
    lps13Generator hq i (lps13ConjIndex a) = (lps13Generator hq i a)⁻¹ := by
  have h13 : (13 : ZMod q) ≠ 0 := by
    simpa using (ZMod.natCast_eq_zero_iff 13 q).not.mpr
      (Nat.not_dvd_of_pos_of_lt (by decide) hq)
  have hgl : lps13GL hq i a * lps13GL hq i (lps13ConjIndex a) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 13 h13) := by
    apply Units.ext
    have hm := lps13Matrix_mul_conj i a
    simp only [Units.val_mul, lps13GL, Matrix.GeneralLinearGroup.val_mkOfDetNeZero,
      Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0]
    rw [hm]
    ext j k
    by_cases hjk : j = k <;> simp [Matrix.scalar, Matrix.diagonal, hjk]
  apply eq_inv_of_mul_eq_one_right
  change Matrix.ProjGenLinGroup.mk (lps13GL hq i a) *
    Matrix.ProjGenLinGroup.mk (lps13GL hq i (lps13ConjIndex a)) = 1
  rw [← map_mul, hgl, Matrix.ProjGenLinGroup.mk_scalar]

theorem lps13Generators_card : (lps13Generators hq i).card = 14 := by
  classical
  rw [lps13Generators, Finset.card_image_of_injective _ (lps13Generator_injective hq i)]
  simp

theorem one_not_mem_lps13Generators : 1 ∉ lps13Generators hq i := by
  classical
  simp only [lps13Generators, Finset.mem_image, Finset.mem_univ, true_and, not_exists]
  exact lps13Generator_ne_one hq i

theorem lps13Generators_inv_mem {s : Matrix.ProjGenLinGroup (Fin 2) (ZMod q)}
    (hs : s ∈ lps13Generators hq i) : s⁻¹ ∈ lps13Generators hq i := by
  classical
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hs
  exact Finset.mem_image.mpr ⟨lps13ConjIndex a, Finset.mem_univ _, lps13Generator_conj hq i a⟩

/-- Neighbors are exactly the right translates by the fourteen projective generators. -/
theorem lps13Graph_neighborSet (v : Matrix.ProjGenLinGroup (Fin 2) (ZMod q)) :
    (lps13Graph hq i).neighborSet v = (v * ·) '' (lps13Generators hq i : Set _) := by
  classical
  ext w
  rw [SimpleGraph.mem_neighborSet, lps13Graph, SimpleGraph.mulCayley_adj]
  constructor
  · rintro ⟨_, h | h⟩
    · exact ⟨v⁻¹ * w, h, by simp⟩
    · refine ⟨(w⁻¹ * v)⁻¹, lps13Generators_inv_mem hq i h, ?_⟩
      simp
  · rintro ⟨s, hs, rfl⟩
    refine ⟨?_, Or.inl (by simpa using hs)⟩
    intro he
    have hs1 : s = 1 := by
      apply mul_left_cancel (a := v)
      simpa using he.symm
    exact one_not_mem_lps13Generators hq i (hs1 ▸ hs)

/-- The fixed-13 PGL Cayley graph is 14-regular in the original OPG encard predicate. -/
theorem lps13Graph_regular14 : IsRegularOfDegree (lps13Graph hq i) 14 := by
  intro v
  rw [lps13Graph_neighborSet, (mul_right_injective v).encard_image,
    Set.encard_coe_eq_coe_finsetCard, lps13Generators_card]

theorem lps13Graph_finite_vertices : Finite (Matrix.ProjGenLinGroup (Fin 2) (ZMod q)) :=
  Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective

theorem lps13Graph_loopless (v : Matrix.ProjGenLinGroup (Fin 2) (ZMod q)) :
    ¬ (lps13Graph hq i).Adj v v := SimpleGraph.irrefl _

end FiniteField

end OPG37364


end Stage17BSource10

noncomputable section Stage17BSource11
-- Source: OPG37364.LPS13CycleWords
set_option autoImplicit false

namespace OPG37364
namespace Girth13

theorem reduced_iff_chain (w : List (Fin 14)) :
    lps13WordReduced w ↔ w.IsChain (fun a b => b ≠ lps13ConjIndex a) := by
  induction w with
  | nil => simp [lps13WordReduced]
  | cons a w ih =>
    cases w with
    | nil => simp [lps13WordReduced]
    | cons b w => simpa only [lps13WordReduced, List.isChain_cons_cons] using and_congr Iff.rfl ih

variable {q : ℕ} [Fact q.Prime] (hq : 13 < q) (i : LPS13Root q)
local notation "PGL" => Matrix.ProjGenLinGroup (Fin 2) (ZMod q)

theorem edge_label {u v : PGL} (h : (lps13Graph hq i).Adj u v) :
    ∃ a : Fin 14, v = u * lps13Generator hq i a := by
  classical
  rw [lps13Graph, SimpleGraph.mulCayley_adj] at h
  obtain ⟨_, h | h⟩ := h
  · obtain ⟨a, _, ha⟩ := Finset.mem_image.mp h
    exact ⟨a, by rw [ha]; simp⟩
  · obtain ⟨a, _, ha⟩ := Finset.mem_image.mp h
    exact ⟨lps13ConjIndex a, by rw [lps13Generator_conj, ha]; simp⟩

theorem telescope (v : ℕ → PGL) (a : ℕ → Fin 14) (m : ℕ)
    (he : ∀ j < m, v (j+1) = v j * lps13Generator hq i (a j)) :
    v 0 * (((List.range m).map a).map (lps13Generator hq i)).prod = v m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.map_append, List.prod_append]
    simp only [List.map_singleton, List.prod_singleton]
    rw [← mul_assoc, ih (fun j hj => he j (by omega)), ← he m (by omega)]

theorem cycle_word (vs : List PGL) (hc : IsCycleList (lps13Graph hq i) vs) :
    ∃ w : List (Fin 14), w.length = vs.length ∧ lps13WordReduced w ∧
      (w.map (lps13Generator hq i)).prod = 1 := by
  classical
  obtain ⟨x, y, middle, rfl, hlen, hnodup, hchain, hclose⟩ := hc
  let vs : List PGL := x :: (middle ++ [y])
  let m := vs.length
  have hm : 3 ≤ m := hlen
  have hn : vs.Nodup := hnodup
  let v : ℕ → PGL := fun j => if hj : j < m then vs[j] else x
  have v0 : v 0 = x := by simp [v, vs, m]
  have vm : v m = x := by simp [v]
  have edges : ∀ j < m, (lps13Graph hq i).Adj (v j) (v (j+1)) := by
    intro j hj
    by_cases hj1 : j + 1 < m
    · have he := (List.isChain_iff_getElem.mp hchain) j hj1
      simpa only [v, dif_pos hj, dif_pos hj1] using he
    · have heq : j = middle.length + 1 := by simp only [m, vs, List.length_cons,
        List.length_append, List.length_nil] at hj hj1; omega
      subst j
      simpa [v, m, vs] using hclose
  have distinct2 : ∀ j, j + 1 < m → v j ≠ v (j+2) := by
    intro j hj he
    have hj0 : j < m := by omega
    by_cases hj2 : j + 2 < m
    · have hi : (⟨j, hj0⟩ : Fin vs.length) = ⟨j+2, hj2⟩ := hn.injective_get
        (by simpa only [v, dif_pos hj0, dif_pos hj2, List.get_eq_getElem] using he)
      have hi' : j = j + 2 := congrArg Fin.val hi
      omega
    · have hx : v (j+2) = x := by simp only [v, dif_neg hj2]
      have hi : (⟨j, hj0⟩ : Fin vs.length) = ⟨0, by omega⟩ := hn.injective_get (by
        simpa only [v, dif_pos hj0, List.get_eq_getElem, vs, List.getElem_cons_zero] using he.trans hx)
      have hi' : j = 0 := congrArg Fin.val hi
      omega
  have labels : ∀ j : ℕ, ∃ a : Fin 14,
      j < m → v (j+1) = v j * lps13Generator hq i a := by
    intro j
    by_cases hj : j < m
    · obtain ⟨a, ha⟩ := edge_label hq i (edges j hj)
      exact ⟨a, fun _ => ha⟩
    · exact ⟨0, fun h => (hj h).elim⟩
  choose a ha using labels
  refine ⟨(List.range m).map a, by simp [m, vs], ?_, ?_⟩
  · rw [reduced_iff_chain, List.isChain_iff_getElem]
    intro j hj
    simp only [List.length_map, List.length_range] at hj
    simp only [List.getElem_map, List.getElem_range]
    intro he
    apply distinct2 j hj
    calc
      v j = (v j * lps13Generator hq i (a j)) *
          lps13Generator hq i (lps13ConjIndex (a j)) := by rw [lps13Generator_conj]; simp
      _ = v (j+2) := by rw [← ha j (by omega), ← he, ← ha (j+1) hj]
  · have ht := telescope hq i v a m ha
    rw [v0, vm] at ht
    exact mul_left_cancel (by simpa using ht : x * _ = x * 1)

end Girth13
end OPG37364


end Stage17BSource11

noncomputable section Stage17BSource12
-- Source: OPG37364.LPS13GirthPlatform
set_option autoImplicit false
open scoped Quaternion

namespace OPG37364
namespace Girth13

theorem word_im_nonzero (w : List (Fin 14)) (hne : w ≠ [])
    (hr : lps13WordReduced w) :
    (lps13WordProduct w).imI ≠ 0 ∨ (lps13WordProduct w).imJ ≠ 0 ∨
      (lps13WordProduct w).imK ≠ 0 := by
  by_contra h
  push Not at h
  have hn := ScaledWordInjectivity.word_norm w
  rw [Quaternion.normSq_def', h.1, h.2.1, h.2.2] at hn
  have heq : (lps13WordProduct w).re ^ 2 = (13 : ℤ)^w.length := by simpa using hn
  have hd : (13 : ℤ) ∣ (lps13WordProduct w).re ^ 2 := by
    rw [heq]
    exact dvd_pow_self _ (List.length_pos_iff.mpr hne).ne'
  have hp : Prime (13 : ℤ) := by norm_num
  have hd' := hp.dvd_of_dvd_pow hd
  exact lps13_reduced_word_not_all_coords_dvd13 w hr
    ⟨hd', by simp [h.1], by simp [h.2.1], by simp [h.2.2]⟩

variable {q : ℕ} [Fact q.Prime] (hq : 13 < q) (i : LPS13Root q)

theorem matrix_one : lps13QuaternionMatrix i.val (1 : Quaternion ℤ) = 1 := by
  ext j k
  fin_cases j <;> fin_cases k <;> simp [lps13QuaternionMatrix]

theorem matrix_mul (x y : Quaternion ℤ) :
    lps13QuaternionMatrix i.val (x * y) =
      lps13QuaternionMatrix i.val x * lps13QuaternionMatrix i.val y := by
  ext j k
  fin_cases j <;> fin_cases k <;>
    simp [lps13QuaternionMatrix, Quaternion.re_mul, Quaternion.imI_mul,
      Quaternion.imJ_mul, Quaternion.imK_mul, Matrix.mul_apply, Fin.sum_univ_two] <;>
    ring_nf <;> rw [i.property] <;> ring

noncomputable def eval (w : List (Fin 14)) := (w.map (lps13Generator hq i)).prod
noncomputable def glEval (w : List (Fin 14)) := (w.map (lps13GL hq i)).prod

theorem glEval_val (w : List (Fin 14)) :
    (glEval hq i w).val = lps13QuaternionMatrix i.val (lps13WordProduct w) := by
  induction w with
  | nil => simp [glEval, lps13WordProduct, matrix_one]
  | cons a w ih =>
    simpa only [glEval, lps13WordProduct, List.map_cons, List.prod_cons,
      Units.val_mul, lps13GL, Matrix.GeneralLinearGroup.val_mkOfDetNeZero,
      lps13Matrix, matrix_mul] using
      congrArg (fun M => lps13Matrix i a * M) ih

theorem mk_glEval (w : List (Fin 14)) :
    Matrix.ProjGenLinGroup.mk (glEval hq i w) = eval hq i w := by
  change Matrix.ProjGenLinGroup.mk ((w.map (lps13GL hq i)).prod) =
    (w.map (fun a => Matrix.ProjGenLinGroup.mk (lps13GL hq i a))).prod
  rw [map_list_prod, List.map_map]
  rfl

theorem word_det (w : List (Fin 14)) :
    (lps13QuaternionMatrix i.val (lps13WordProduct w)).det = (13 : ZMod q) ^ w.length := by
  rw [lps13QuaternionMatrix_det, ScaledWordInjectivity.word_norm]
  norm_cast

include hq in
theorem word_det_ne_zero (w : List (Fin 14)) :
    (lps13QuaternionMatrix i.val (lps13WordProduct w)).det ≠ 0 := by
  rw [word_det]
  apply pow_ne_zero
  simpa using (ZMod.natCast_eq_zero_iff 13 q).not.mpr
    (Nat.not_dvd_of_pos_of_lt (by decide) hq)

theorem closed_word_im_dvd (w : List (Fin 14)) (he : eval hq i w = 1) :
    (q : ℤ) ∣ (lps13WordProduct w).imI ∧
    (q : ℤ) ∣ (lps13WordProduct w).imJ ∧
    (q : ℤ) ∣ (lps13WordProduct w).imK := by
  have he' : Matrix.ProjGenLinGroup.mk (1 : Matrix.GeneralLinearGroup (Fin 2) (ZMod q)) =
      Matrix.ProjGenLinGroup.mk (glEval hq i w) := by rw [mk_glEval, he]; rfl
  obtain ⟨r, hr⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp he'
  have hm := congrArg Units.val hr
  rw [glEval_val] at hm
  simp only [one_mul, Matrix.GeneralLinearGroup.coe_scalar] at hm
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) (ZMod q) => M 0 0) hm
  have h11 := congrArg (fun M : Matrix (Fin 2) (Fin 2) (ZMod q) => M 1 1) hm
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) (ZMod q) => M 0 1) hm
  have h10 := congrArg (fun M : Matrix (Fin 2) (Fin 2) (ZMod q) => M 1 0) hm
  simp [lps13QuaternionMatrix, Matrix.scalar, Matrix.diagonal] at h00 h11 h01 h10
  have h2 : (2 : ZMod q) ≠ 0 := by
    simpa using (ZMod.natCast_eq_zero_iff 2 q).not.mpr
      (Nat.not_dvd_of_pos_of_lt (by decide) (by omega))
  have hi : i.val ≠ 0 := by intro hi; have hh := i.property; rw [hi] at hh; simp at hh
  have hI : ((lps13WordProduct w).imI : ZMod q) = 0 := by
    apply mul_left_cancel₀ (mul_ne_zero h2 hi)
    linear_combination h11 - h00
  have hJ : ((lps13WordProduct w).imJ : ZMod q) = 0 := by
    apply mul_left_cancel₀ h2
    linear_combination h10 - h01
  have hK : ((lps13WordProduct w).imK : ZMod q) = 0 := by
    apply mul_left_cancel₀ (mul_ne_zero h2 hi)
    linear_combination -h01 - h10
  exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp hI,
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp hJ,
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp hK⟩

omit [Fact q.Prime] in
theorem sq_le_of_dvd_ne_zero {a : ℤ} (ha : a ≠ 0) (hd : (q : ℤ) ∣ a) :
    (q : ℤ)^2 ≤ a^2 := by
  obtain ⟨k, rfl⟩ := hd
  have hk : k ≠ 0 := by intro h; simp [h] at ha
  have hk1 : (1 : ℤ) ≤ k^2 := by
    have : k ≤ -1 ∨ 1 ≤ k := by omega
    rcases this with h | h <;> nlinarith
  nlinarith [mul_nonneg (sq_nonneg (q : ℤ)) (sub_nonneg.mpr hk1)]

theorem closed_reduced_word_bound (w : List (Fin 14)) (hne : w ≠ [])
    (hr : lps13WordReduced w) (he : eval hq i w = 1) : q^2 ≤ 13^w.length := by
  obtain ⟨hI, hJ, hK⟩ := closed_word_im_dvd hq i w he
  have hn := ScaledWordInjectivity.word_norm w
  rw [Quaternion.normSq_def'] at hn
  have hh : (q : ℤ)^2 ≤ (13 : ℤ)^w.length := by
    obtain h | h | h := word_im_nonzero w hne hr
    · have hb := sq_le_of_dvd_ne_zero h hI
      nlinarith [sq_nonneg (lps13WordProduct w).re,
        sq_nonneg (lps13WordProduct w).imJ, sq_nonneg (lps13WordProduct w).imK]
    · have hb := sq_le_of_dvd_ne_zero h hJ
      nlinarith [sq_nonneg (lps13WordProduct w).re,
        sq_nonneg (lps13WordProduct w).imI, sq_nonneg (lps13WordProduct w).imK]
    · have hb := sq_le_of_dvd_ne_zero h hK
      nlinarith [sq_nonneg (lps13WordProduct w).re,
        sq_nonneg (lps13WordProduct w).imI, sq_nonneg (lps13WordProduct w).imJ]
  exact_mod_cast hh

end Girth13

/-- The original OPG cycle-list girth bound for the existing graph, uniformly in its root. -/
theorem lps13Graph_hasGirthAtLeast_of_pow_lt_sq
    {q : ℕ} [Fact q.Prime] (hq : 13 < q) (i : LPS13Root q)
    (g : ℕ) (hbound : 13^g < q^2) : HasGirthAtLeast (lps13Graph hq i) g := by
  intro vs hc
  obtain ⟨w, hlen, hr, he⟩ := Girth13.cycle_word hq i vs hc
  have hv : 3 ≤ vs.length := by obtain ⟨_, _, _, _, hh, _⟩ := hc; exact hh
  have hw : w ≠ [] := by intro h; simp [h] at hlen; omega
  have hb := Girth13.closed_reduced_word_bound hq i w hw hr he
  rw [hlen] at hb
  by_contra h
  have hm : vs.length ≤ g := by omega
  have hp : 13^vs.length ≤ 13^g := Nat.pow_le_pow_right (by decide) hm
  omega

/-- A deliberately coarse integer threshold for eventual prime selection. -/
theorem lps13Graph_hasGirthAtLeast_of_pow_lt
    {q : ℕ} [Fact q.Prime] (hq : 13 < q) (i : LPS13Root q)
    (g : ℕ) (hbound : 13^g < q) : HasGirthAtLeast (lps13Graph hq i) g := by
  apply lps13Graph_hasGirthAtLeast_of_pow_lt_sq hq i g
  have hsq : q ≤ q^2 := by nlinarith
  omega

end OPG37364




end Stage17BSource12

noncomputable section Stage17BSource13
-- Source: OPG37364.LPS13ClosedWordCount
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace OPG37364.ClosedWordCount

variable {q : ℕ} [Fact q.Prime] (hq : 13 < q) (i : LPS13Root q)

def Words (m : ℕ) :=
  {w : Fin m → Fin 14 // lps13WordReduced (List.ofFn w) ∧
    lps13ProjectiveWordProduct hq i (List.ofFn w)=1}

instance (m : ℕ) : Fintype (Words hq i m) := inferInstanceAs (Fintype {w // _})

theorem card_words (m : ℕ) :
    Fintype.card (Words hq i m)=lps13ClosedReducedWordCount hq i m := by
  simp [Words,lps13ClosedReducedWordCount,Fintype.card_subtype]
  exact Fintype.card_subtype _

theorem word_divisibility (r : ℕ) (w : Words hq i (2*r)) :
    (q : ℤ) ∣ (lps13WordProduct (List.ofFn w.val)).imI ∧
    (q : ℤ) ∣ (lps13WordProduct (List.ofFn w.val)).imJ ∧
    (q : ℤ) ∣ (lps13WordProduct (List.ofFn w.val)).imK :=
  Girth13.closed_word_im_dvd hq i _ w.property.2

def wordToQuad (r : ℕ) (w : Words hq i (2*r)) : QuaternionCount.Quadruples q (13^r) :=
  let a := lps13WordProduct (List.ofFn w.val)
  ⟨(a.re,a.imI/q,a.imJ/q,a.imK/q), by
    obtain ⟨hI,hJ,hK⟩ := word_divisibility hq i r w
    have eI := Int.ediv_mul_cancel hI
    have eJ := Int.ediv_mul_cancel hJ
    have eK := Int.ediv_mul_cancel hK
    have hn := ScaledWordInjectivity.word_norm (List.ofFn w.val)
    rw [Quaternion.normSq_def'] at hn
    simp only [List.length_ofFn] at hn
    change a.re^2+a.imI^2+a.imJ^2+a.imK^2=(13 : ℤ)^(2*r) at hn
    change a.imI/(q : ℤ)*(q : ℤ)=a.imI at eI
    change a.imJ/(q : ℤ)*(q : ℤ)=a.imJ at eJ
    change a.imK/(q : ℤ)*(q : ℤ)=a.imK at eK
    push_cast
    calc
      a.re^2+(q : ℤ)^2*((a.imI/q)^2+(a.imJ/q)^2+(a.imK/q)^2) =
          a.re^2+(a.imI/q*q)^2+(a.imJ/q*q)^2+(a.imK/q*q)^2 := by ring
      _ = (13 : ℤ)^(2*r) := by rw [eI,eJ,eK]; exact hn
      _ = ((13 : ℤ)^r)^2 := by rw [←pow_mul]; congr 1; omega⟩

theorem wordToQuad_injective (r : ℕ) : Function.Injective (wordToQuad hq i r) := by
  intro u v he
  have hc := congrArg Subtype.val he
  have hR := congrArg Prod.fst hc
  have hI := congrArg (fun x : ℤ × (ℤ × (ℤ × ℤ)) => x.2.1) hc
  have hJ := congrArg (fun x : ℤ × (ℤ × (ℤ × ℤ)) => x.2.2.1) hc
  have hK := congrArg (fun x : ℤ × (ℤ × (ℤ × ℤ)) => x.2.2.2) hc
  obtain ⟨uI,uJ,uK⟩ := word_divisibility hq i r u
  obtain ⟨vI,vJ,vK⟩ := word_divisibility hq i r v
  have hp : lps13WordProduct (List.ofFn u.val)=lps13WordProduct (List.ofFn v.val) := by
    apply Quaternion.ext
    · exact hR
    · simpa only [wordToQuad,Int.ediv_mul_cancel uI,Int.ediv_mul_cancel vI] using
        congrArg (fun x : ℤ => x*q) hI
    · simpa only [wordToQuad,Int.ediv_mul_cancel uJ,Int.ediv_mul_cancel vJ] using
        congrArg (fun x : ℤ => x*q) hJ
    · simpa only [wordToQuad,Int.ediv_mul_cancel uK,Int.ediv_mul_cancel vK] using
        congrArg (fun x : ℤ => x*q) hK
  have hw := (lps13_scaled_reduced_word_product_injective 0 0 _ _
    u.property.1 v.property.1 (by simpa using hp)).2
  exact Subtype.ext (List.ofFn_injective hw)

theorem closed_count_le_Rq (r : ℕ) :
    lps13ClosedReducedWordCount hq i (2*r) ≤ QuaternionCount.Rq q (13^r) := by
  letI : Fact (0 < q) := ⟨by omega⟩
  calc
    lps13ClosedReducedWordCount hq i (2*r) = Nat.card (Words hq i (2*r)) := by
      rw [Nat.card_eq_fintype_card,card_words]
    _ ≤ Nat.card (QuaternionCount.Quadruples q (13^r)) :=
      Nat.card_le_card_of_injective _ (wordToQuad_injective hq i r)
    _ ≤ QuaternionCount.Rq q (13^r) := QuaternionCount.card_quadruples_le_Rq _ _ (by omega)

theorem scale_of_count_pos (r : ℕ) (hr : 0 < r)
    (hc : 0 < lps13ClosedReducedWordCount hq i (2*r)) : q ≤ 13^r := by
  have hcard : 0 < Fintype.card (Words hq i (2*r)) := by rwa [card_words]
  obtain ⟨w⟩ := Fintype.card_pos_iff.mp hcard
  have hne : List.ofFn w.val ≠ [] := by
    intro h
    have := congrArg List.length h
    simp only [List.length_ofFn,List.length_nil] at this
    omega
  have hb := Girth13.closed_reduced_word_bound hq i _ hne w.property.1 w.property.2
  simp only [List.length_ofFn] at hb
  have he : 13^(2*r)=(13^r)^2 := by rw [←pow_mul]; congr 1; omega
  rw [he] at hb
  exact (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp hb

theorem closed_count_pow_ten_le :
    ∃ D : ℕ, 0 < D ∧ ∀ {q : ℕ} [Fact q.Prime] (hq : 13 < q)
      (i : LPS13Root q) (r : ℕ), 0 < r →
      lps13ClosedReducedWordCount hq i (2*r)^10*q^34 ≤
        D*(13^(24*r)+13^(14*r)*q^20) := by
  obtain ⟨D,hD,hbound⟩ := QuaternionCount.quaternion_count_pow_ten_le
  refine ⟨D,hD,?_⟩
  intro q hp hq i r hr
  by_cases hc : 0 < lps13ClosedReducedWordCount hq i (2*r)
  · have hqt := scale_of_count_pos hq i r hr hc
    have hnd : ¬q∣13^r := by
      intro h
      exact (Nat.not_dvd_of_pos_of_lt (by decide) hq) (hp.out.dvd_of_dvd_pow h)
    have hb := hbound q (13^r) hp.out (by omega) hnd hqt
    have hh := Nat.mul_le_mul_right (q^34)
      (Nat.pow_le_pow_left (closed_count_le_Rq hq i r) 10)
    apply hh.trans
    simpa [←pow_mul,Nat.mul_comm r] using hb
  · have hz : lps13ClosedReducedWordCount hq i (2*r)=0 := by omega
    simp [hz]

end OPG37364.ClosedWordCount


end

end Stage17BSource13

noncomputable section Stage17BSource14
-- Source: OPG37364.LPS13VertexCard
set_option autoImplicit false
noncomputable section

namespace OPG37364

theorem lps13_vertex_card_le_two_mul_cube {q : ℕ} [Fact q.Prime] :
    Fintype.card (LPS13Vertex q) ≤ 2*q^3 := by
  classical
  let VertexGL := Matrix.GeneralLinearGroup (Fin 2) (ZMod q)
  let Z := Subgroup.center VertexGL
  let f : (ZMod q)ˣ → Z := fun u =>
    ⟨Matrix.GeneralLinearGroup.scalar (Fin 2) u, by
      dsimp [Z,VertexGL]
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨u,rfl⟩⟩
  have hf : Function.Injective f := by
    intro u v huv
    have he := congrArg (fun z : Z => ((z.val.val : Matrix (Fin 2) (Fin 2) (ZMod q)) 0 0)) huv
    apply Units.ext
    simpa [f,Matrix.GeneralLinearGroup.coe_scalar] using he
  have hZ : q-1 ≤ Nat.card Z := by
    have hh := Nat.card_le_card_of_injective f hf
    simpa only [Nat.card_eq_fintype_card,ZMod.card_units] using hh
  have hGL : Nat.card VertexGL ≤ q^4 := by
    have hh := Nat.card_le_card_of_injective
      (fun g : VertexGL => (g.val : Matrix (Fin 2) (Fin 2) (ZMod q))) Units.val_injective
    convert hh using 1
    simp [Nat.card_eq_fintype_card,Matrix,Fintype.card_fun,ZMod.card,←pow_mul]
  have he := Subgroup.card_eq_card_quotient_mul_card_subgroup Z
  have hP : Nat.card VertexGL = Fintype.card (LPS13Vertex q)*Nat.card Z := by
    convert he using 1
    rw [show Nat.card (VertexGL ⧸ Z)=Fintype.card (LPS13Vertex q) from
      (Nat.card_eq_fintype_card : Nat.card (LPS13Vertex q)=_)]
  have hmult : Fintype.card (LPS13Vertex q)*(q-1) ≤ q^4 := by
    exact (Nat.mul_le_mul_left _ hZ).trans (hP ▸ hGL)
  have hq : 2 ≤ q := (Fact.out : q.Prime).two_le
  have hh : q ≤ 2*(q-1) := by omega
  have hfinal : q*Fintype.card (LPS13Vertex q) ≤ q*(2*q^3) := by
    calc
      q*Fintype.card (LPS13Vertex q) ≤ (2*(q-1))*Fintype.card (LPS13Vertex q) :=
        Nat.mul_le_mul_right _ hh
      _ = 2*(Fintype.card (LPS13Vertex q)*(q-1)) := by ring
      _ ≤ 2*q^4 := Nat.mul_le_mul_left 2 hmult
      _ = q*(2*q^3) := by ring
  exact Nat.le_of_mul_le_mul_left hfinal (by omega)

end OPG37364

end

end Stage17BSource14

noncomputable section Stage17BSource15
-- Source: OPG37364.LPS13TracePolynomial
set_option autoImplicit false
open scoped BigOperators
open Polynomial

namespace OPG37364.Trace13
local notation "P" => lps13NonbacktrackingPolynomial

theorem P_zero : P 0 = 1 := rfl
theorem P_one : P 1 = X := rfl
theorem P_rec (n : ℕ) : P (n+2) = X * P (n+1) - 13 * P n := rfl

theorem P_add (n m : ℕ) :
    P (n+m+2) = P (n+1) * P (m+1) - 13 * P n * P m := by
  induction m using Nat.twoStepInduction with
  | zero =>
    change P (n+2) = P (n+1) * X - 13 * P n * 1
    rw [P_rec]
    ring
  | one =>
    change P (n+3) = P (n+1) * (X*X-13*1) - 13 * P n * X
    rw [show n+3 = (n+1)+2 by omega, P_rec (n+1), P_rec n]
    ring
  | more m ih₀ ih₁ =>
    rw [show n+(m+2)+2 = (n+m+2)+2 by omega, P_rec]
    rw [show n+m+2+1 = n+(m+1)+2 by omega, ih₁, ih₀]
    rw [show m+2+1 = (m+1)+2 by omega, P_rec (m+1), P_rec m]
    ring

theorem P_square_step (m : ℕ) :
    P (m+1)^2 = P (2*(m+1)) + 13 * P m^2 := by
  have h := P_add m m
  rw [show m+m+2 = 2*(m+1) by omega] at h
  linear_combination -h

theorem P_square (m : ℕ) :
    P m^2 = ∑ j ∈ Finset.range (m+1), (13 : Polynomial ℝ)^j * P (2*m-2*j) := by
  induction m with
  | zero => simp [P_zero]
  | succ m ih =>
    rw [P_square_step, ih, Finset.mul_sum]
    conv_rhs => rw [Finset.sum_range_succ']
    simp only [Nat.mul_zero, Nat.sub_zero, pow_zero, one_mul]
    rw [add_comm (P (2*(m+1)))]
    apply congrArg (fun z => z + P (2*(m+1)))
    apply Finset.sum_congr rfl
    intro j hj
    rw [show 2*(m+1)-2*(j+1) = 2*m-2*j by omega, pow_succ']
    ring

/-- Parity sum in increasing index order, avoiding subtraction in its summands. -/
def paritySum {R : Type*} [AddCommMonoid R] (b : ℕ → R) (m : ℕ) : R :=
  ∑ j ∈ Finset.range (m/2+1), b (m%2+2*j)

theorem parity_zero {R : Type*} [AddCommMonoid R] (b : ℕ → R) :
    paritySum b 0 = b 0 := by simp [paritySum]

theorem parity_one {R : Type*} [AddCommMonoid R] (b : ℕ → R) :
    paritySum b 1 = b 1 := by simp [paritySum]

theorem parity_rec {R : Type*} [AddCommMonoid R] (b : ℕ → R) (m : ℕ) :
    paritySum b (m+2) = paritySum b m + b (m+2) := by
  have hd : (m+2)/2 = m/2+1 := by omega
  have hm : (m+2)%2 = m%2 := by omega
  have he : m%2+2*(m/2+1) = m+2 := by omega
  simp only [paritySum, hd, hm, Finset.sum_range_succ, he]

end OPG37364.Trace13


end Stage17BSource15

noncomputable section Stage17BSource16
-- Source: OPG37364.LPS13TraceWords
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace OPG37364.Trace13

theorem sum_words_succ {R : Type*} [AddCommMonoid R]
    (n : ℕ) (f : List (Fin 14) → R) :
    (∑ w : Fin (n+1) → Fin 14, f (List.ofFn w)) =
      ∑ a : Fin 14, ∑ w : Fin n → Fin 14, f (a :: List.ofFn w) := by
  simpa [Fintype.sum_prod_type, Fin.consEquiv, List.ofFn_cons] using
    (Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n+1) => Fin 14))
      (fun w => f (List.ofFn w))).symm

theorem conj_eq_iff (a b : Fin 14) :
    b = lps13ConjIndex a ↔ a = lps13ConjIndex b := by
  constructor
  · intro h
    exact ((congrArg lps13ConjIndex h).trans (lps13ConjIndex_involutive a)).symm
  · intro h
    exact ((congrArg lps13ConjIndex h).trans (lps13ConjIndex_involutive b)).symm

variable {q : ℕ} [Fact q.Prime]
local notation "G" => LPS13Vertex q
local notation "Mat" => Matrix G G ℝ
local notation "T" => lps13TranslationMatrix (q := q)

theorem translation_one : T 1 = (1 : Mat) := by
  ext x y
  simp [lps13TranslationMatrix, Matrix.one_apply]

theorem translation_mul (s t : G) : T (s*t) = T s * T t := by
  ext x y
  simp only [lps13TranslationMatrix, Matrix.mul_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, mul_assoc]

theorem translation_trace (s : G) :
    Matrix.trace (T s) = if s=1 then (Fintype.card G : ℝ) else 0 := by
  simp [Matrix.trace, Matrix.diag, lps13TranslationMatrix, mul_eq_left]

variable (hq : 13 < q) (i : LPS13Root q)
local notation "ev" => lps13ProjectiveWordProduct hq i
local notation "gen" => lps13Generator hq i
local notation "B" => lps13ReducedWordMatrix hq i
local notation "A" => SimpleGraph.adjMatrix ℝ (lps13Graph hq i)

theorem eval_nil : ev [] = 1 := rfl
theorem eval_cons (a : Fin 14) (w : List (Fin 14)) :
    ev (a::w) = gen a * ev w := by simp [lps13ProjectiveWordProduct]

def wordTerm (w : List (Fin 14)) : Mat :=
  if lps13WordReduced w then T (ev w) else 0

theorem B_zero : B 0 = 1 := by
  simp [lps13ReducedWordMatrix, List.ofFn_zero, lps13WordReduced, eval_nil, translation_one]

theorem B_one_sum : B 1 = ∑ a : Fin 14, T (gen a) := by
  change (∑ w : Fin 1 → Fin 14, wordTerm hq i (List.ofFn w)) = _
  rw [sum_words_succ 0 (wordTerm hq i)]
  simp [wordTerm, List.ofFn_zero, lps13WordReduced, eval_cons, eval_nil]

theorem adjacency_sum : A = ∑ a : Fin 14, T (gen a) := by
  ext x y
  have hadj : (lps13Graph hq i).Adj x y ↔ ∃ a, x * gen a = y := by
    rw [← SimpleGraph.mem_neighborSet, lps13Graph_neighborSet]
    simp [lps13Generators]
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨a, by rw [ha]; simp⟩
    · rintro ⟨a, ha⟩
      exact ⟨a, by rw [← ha]; simp⟩
  simp only [SimpleGraph.adjMatrix_apply, Matrix.sum_apply, lps13TranslationMatrix]
  by_cases he : ∃ a, x * gen a = y
  · obtain ⟨a, rfl⟩ := he
    have heq : ∀ b, x * gen b = x * gen a ↔ b=a := by
      intro b
      exact (mul_left_cancel_iff).trans (lps13Generator_injective hq i).eq_iff
    have ha := hadj.mpr ⟨a, rfl⟩
    simp [ha, heq]
  · have hn : ¬ (lps13Graph hq i).Adj x y := fun h => he (hadj.mp h)
    simp [hn, show ∀ a, x * gen a ≠ y from not_exists.mp he]

theorem B_one : B 1 = A := (B_one_sum hq i).trans (adjacency_sum hq i).symm

theorem term_partition (a b : Fin 14) (w : List (Fin 14)) :
    T (gen a) * wordTerm hq i (b::w) = wordTerm hq i (a::b::w) +
      if b = lps13ConjIndex a ∧ lps13WordReduced (b::w) then T (ev w) else 0 := by
  by_cases hr : lps13WordReduced (b::w)
  · by_cases hb : b = lps13ConjIndex a
    · subst b
      have hn : ¬ lps13WordReduced (a::lps13ConjIndex a::w) := by
        change ¬ (lps13ConjIndex a ≠ lps13ConjIndex a ∧ _)
        simp
      simp only [wordTerm, if_neg hn, true_and, if_pos hr, zero_add]
      rw [eval_cons, translation_mul, ← mul_assoc, ← translation_mul,
        lps13Generator_conj, mul_inv_cancel, translation_one, one_mul]
    · have hg : lps13WordReduced (a::b::w) := ⟨hb, hr⟩
      simp only [wordTerm, if_pos hr, if_pos hg, hb, false_and, if_false, add_zero]
      simp only [eval_cons, translation_mul]
  · have hn : ¬ lps13WordReduced (a::b::w) := fun h => hr h.2
    simp [wordTerm, hr, hn]

def correction (n : ℕ) : Mat :=
  ∑ w : Fin n → Fin 14, ∑ b : Fin 14,
    if lps13WordReduced (b :: List.ofFn w) then T (ev (List.ofFn w)) else 0

theorem forbidden_sum (n : ℕ) :
    (∑ a : Fin 14, ∑ b : Fin 14, ∑ w : Fin n → Fin 14,
      if b=lps13ConjIndex a ∧ lps13WordReduced (b::List.ofFn w)
      then T (ev (List.ofFn w)) else 0) = correction hq i n := by
  rw [Finset.sum_comm]
  unfold correction
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  trans ∑ a : Fin 14, if a=lps13ConjIndex b ∧ lps13WordReduced (b::List.ofFn w)
    then T (ev (List.ofFn w)) else 0
  · apply Finset.sum_congr rfl
    intro a _
    simp only [conj_eq_iff a b]
  · by_cases hr : lps13WordReduced (b::List.ofFn w) <;> simp [hr]

theorem B_partition (n : ℕ) : A * B (n+1) = B (n+2) + correction hq i n := by
  rw [adjacency_sum]
  change (∑ a : Fin 14, T (gen a)) *
    (∑ w : Fin (n+1) → Fin 14, wordTerm hq i (List.ofFn w)) = _
  rw [sum_words_succ n (wordTerm hq i)]
  change (∑ a : Fin 14, T (gen a)) *
    (∑ b : Fin 14, ∑ w : Fin n → Fin 14, wordTerm hq i (b::List.ofFn w)) = _
  simp_rw [Finset.sum_mul, Finset.mul_sum, term_partition, Finset.sum_add_distrib]
  rw [forbidden_sum]
  congr 1
  change _ = ∑ w : Fin (n+2) → Fin 14, wordTerm hq i (List.ofFn w)
  rw [sum_words_succ (n+1) (wordTerm hq i)]
  apply Finset.sum_congr rfl
  intro a _
  exact (sum_words_succ n (fun w => wordTerm hq i (a::w))).symm

theorem correction_zero : correction hq i 0 = (14 : Mat) := by
  simp [correction, List.ofFn_zero, lps13WordReduced, eval_nil, translation_one,
    nsmul_eq_mul]

theorem thirteen_sum (c : Fin 14) (M : Mat) :
    (∑ b : Fin 14, if c ≠ lps13ConjIndex b then M else 0) = 13 * M := by
  have ht : ∀ b : Fin 14, (if c ≠ lps13ConjIndex b then M else 0) =
      M - (if b=lps13ConjIndex c then M else 0) := by
    intro b
    have hc := conj_eq_iff b c
    by_cases hb : b=lps13ConjIndex c
    · simp only [if_neg (not_not_intro (hc.mpr hb)), if_pos hb, sub_self]
    · have hn : c ≠ lps13ConjIndex b := fun h => hb (hc.mp h)
      simp only [if_pos hn, if_neg hb, sub_zero]
  simp_rw [ht, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  change (14 : Mat) * M - M = 13 * M
  noncomm_ring

theorem correction_succ (n : ℕ) : correction hq i (n+1) = 13 * B (n+1) := by
  rw [correction, sum_words_succ n (fun w => ∑ b : Fin 14,
    if lps13WordReduced (b::w) then T (ev w) else 0)]
  change _ = 13 * (∑ w : Fin (n+1) → Fin 14, wordTerm hq i (List.ofFn w))
  rw [sum_words_succ n (wordTerm hq i)]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro w _
  by_cases hr : lps13WordReduced (c::List.ofFn w)
  · simp only [wordTerm, lps13WordReduced, hr, and_true, if_true]
    exact thirteen_sum c _
  · simp [wordTerm, lps13WordReduced, hr]

theorem B_two : B 2 = A^2 - 14 := by
  have h := B_partition hq i 0
  rw [B_one, correction_zero] at h
  exact eq_sub_of_add_eq (by simpa [pow_two] using h.symm)

theorem B_rec (n : ℕ) : B (n+3) = A * B (n+2) - 13 * B (n+1) := by
  have h := B_partition hq i (n+1)
  rw [correction_succ] at h
  exact eq_sub_of_add_eq h.symm

theorem closed_count_sum (m : ℕ) :
    (lps13ClosedReducedWordCount hq i m : ℝ) =
    ∑ w : Fin m → Fin 14,
      if lps13WordReduced (List.ofFn w) ∧ ev (List.ofFn w)=1 then (1 : ℝ) else 0 := by
  rw [lps13ClosedReducedWordCount, Finset.card_filter, Nat.cast_sum]
  simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

theorem trace_B (m : ℕ) :
    Matrix.trace (B m) = (Fintype.card G : ℝ) * lps13ClosedReducedWordCount hq i m := by
  rw [lps13ReducedWordMatrix, Matrix.trace_sum, closed_count_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  by_cases hr : lps13WordReduced (List.ofFn w) <;>
    by_cases he : ev (List.ofFn w)=1 <;>
      simp [hr, he, translation_trace]

end OPG37364.Trace13

end

end Stage17BSource16

noncomputable section Stage17BSource17
-- Source: OPG37364.LPS13SquaredTrace
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
open Polynomial

namespace OPG37364.Trace13

variable {q : ℕ} [Fact q.Prime] (hq : 13 < q) (i : LPS13Root q)
local notation "G" => LPS13Vertex q
local notation "Mat" => Matrix G G ℝ
local notation "A" => SimpleGraph.adjMatrix ℝ (lps13Graph hq i)
local notation "P" => lps13NonbacktrackingPolynomial
local notation "B" => lps13ReducedWordMatrix hq i
local notation "C" => lps13ClosedReducedWordCount hq i

def evalP (m : ℕ) : Mat := aeval A (P m)
local notation "E" => evalP hq i

theorem evalP_zero : E 0 = 1 := by simp [evalP, P_zero]
theorem evalP_one : E 1 = A := by simp [evalP, P_one]
theorem evalP_rec (m : ℕ) : E (m+2) = A * E (m+1) - 13 * E m := by
  simp only [evalP, P_rec, map_sub, map_mul, map_ofNat, Polynomial.aeval_X]

theorem B_eq_difference (m : ℕ) : B (m+2) = E (m+2) - E m := by
  induction m using Nat.twoStepInduction with
  | zero =>
    rw [B_two, evalP_rec, evalP_one, evalP_zero]
    have hn : (14 : Mat) = 13 + 1 := by norm_num
    simp only [pow_two, mul_one, hn, sub_add_eq_sub_sub]
  | one =>
    rw [B_rec, B_two, B_one, evalP_rec _ _ 1, evalP_rec _ _ 0,
      evalP_one, evalP_zero]
    noncomm_ring
  | more m ih₀ ih₁ =>
    rw [B_rec _ _ (m+1), ih₁, ih₀, evalP_rec _ _ (m+2), evalP_rec _ _ m]
    noncomm_ring

theorem evalP_parity (m : ℕ) : E m = paritySum B m := by
  induction m using Nat.twoStepInduction with
  | zero => rw [parity_zero, B_zero, evalP_zero]
  | one => rw [parity_one, B_one, evalP_one]
  | more m ih₀ ih₁ =>
    rw [parity_rec, ← ih₀, B_eq_difference]
    abel

theorem trace_evalP (m : ℕ) :
    Matrix.trace (E m) = (Fintype.card G : ℝ) *
      ∑ r ∈ Finset.range (m/2+1), (C (m%2+2*r) : ℝ) := by
  rw [evalP_parity, paritySum, Matrix.trace_sum]
  simp_rw [trace_B]
  rw [Finset.mul_sum]

theorem trace_thirteen_pow_mul (j : ℕ) (M : Mat) :
    Matrix.trace ((13 : Mat)^j * M) = (13 : ℝ)^j * Matrix.trace M := by
  have hs : (13 : Mat)^j * M = (13 : ℝ)^j • M := by
    rw [Algebra.smul_def, map_pow, map_ofNat]
  rw [hs, Matrix.trace_smul]
  rfl

theorem squared_trace (m : ℕ) :
    Matrix.trace ((E m)^2) =
      (Fintype.card G : ℝ) * ∑ j ∈ Finset.range (m+1),
        (13 : ℝ)^j * ∑ r ∈ Finset.range (m-j+1), (C (2*r) : ℝ) := by
  have hs := congrArg (fun p : Polynomial ℝ => aeval A p) (P_square m)
  simp only [map_pow, map_sum, map_mul, map_ofNat] at hs
  change (E m)^2 = ∑ j ∈ Finset.range (m+1), (13 : Mat)^j * E (2*m-2*j) at hs
  rw [hs, Matrix.trace_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [trace_thirteen_pow_mul, trace_evalP]
  have hmod : (2*m-2*j)%2 = 0 := by omega
  have hdiv : (2*m-2*j)/2 = m-j := by omega
  simp only [hmod, hdiv, zero_add]
  ring

end OPG37364.Trace13

namespace OPG37364

/-- The square is a matrix square. Counts are of adjacent-reduced closed generator words,
and the vertex-cardinality factor is retained explicitly. -/
theorem lps13_squared_trace_eq_closed_reduced_word_count
    {q : ℕ} [Fact q.Prime] (hq : 13 < q) (i : LPS13Root q) (m : ℕ) :
    Matrix.trace
      ((Polynomial.aeval ((lps13Graph hq i).adjMatrix ℝ)
        (lps13NonbacktrackingPolynomial m))^2) =
      (Fintype.card (LPS13Vertex q) : ℝ) * ∑ j ∈ Finset.range (m+1),
        (13 : ℝ)^j * ∑ r ∈ Finset.range (m-j+1),
          (lps13ClosedReducedWordCount hq i (2*r) : ℝ) :=
  Trace13.squared_trace hq i m

end OPG37364

end

end Stage17BSource17

noncomputable section Stage17BSource18
-- Source: OPG37364.LPS13TraceUpper
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace OPG37364.TraceUpper

theorem sum_pow_mul_le {α : Type*} (s : Finset α) (f : α → ℕ) (Q B : ℕ)
    (h : ∀ a ∈ s, f a^10*Q ≤ B) :
    (∑ a ∈ s, f a)^10*Q ≤ s.card^10*B := by
  by_cases hs : s.Nonempty
  · obtain ⟨a,ha,he⟩ := Finset.exists_mem_eq_sup s hs f
    have hm : ∑ a ∈ s, f a ≤ s.card*s.sup f := by
      apply (Finset.sum_le_sum fun a ha => Finset.le_sup (f := f) ha).trans_eq
      simp
    calc
      (∑ a ∈ s, f a)^10*Q ≤ (s.card*s.sup f)^10*Q :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hm 10)
      _ = s.card^10*((s.sup f)^10*Q) := by ring
      _ ≤ s.card^10*B := Nat.mul_le_mul_left _ (he ▸ h a ha)
  · simp [Finset.not_nonempty_iff_eq_empty.mp hs]

theorem closed_count_zero {q : ℕ} [Fact q.Prime] (hq : 13 < q) (i : LPS13Root q) :
    lps13ClosedReducedWordCount hq i 0=1 := by
  simp [lps13ClosedReducedWordCount,lps13WordReduced,lps13ProjectiveWordProduct]

theorem term_bound :
    ∃ D : ℕ, 0 < D ∧ ∀ {q : ℕ} [Fact q.Prime] (hq : 13 < q)
      (i : LPS13Root q) (k j r : ℕ), q < 13^(2*k+2) → j+r ≤ 5*k →
      (13^j*lps13ClosedReducedWordCount hq i (2*r))^10*q^34 ≤ D*13^(120*k+68) := by
  obtain ⟨D,hD,hcount⟩ := ClosedWordCount.closed_count_pow_ten_le
  refine ⟨2*D+1, by omega, ?_⟩
  intro q hp hq i k j r hqhi hjr
  have hq34 : q^34 ≤ 13^(68*k+68) := by
    have h := Nat.pow_le_pow_left (Nat.le_of_lt hqhi) 34
    convert h using 1 <;> rw [←pow_mul] <;> congr 1 <;> omega
  have hq20 : q^20 ≤ 13^(40*k+40) := by
    have h := Nat.pow_le_pow_left (Nat.le_of_lt hqhi) 20
    convert h using 1 <;> rw [←pow_mul] <;> congr 1 <;> omega
  by_cases hr : r=0
  · subst r
    simp only [Nat.mul_zero,closed_count_zero,mul_one,←pow_mul]
    calc
      13^(j*10)*q^34 ≤ 13^(j*10)*13^(68*k+68) := Nat.mul_le_mul_left _ hq34
      _ = 13^(j*10+68*k+68) := by simp only [pow_add]; ring
      _ ≤ 13^(120*k+68) := Nat.pow_le_pow_right (by decide) (by omega)
      _ ≤ (2*D+1)*13^(120*k+68) := Nat.le_mul_of_pos_left _ (by omega)
  · have hrpos : 0<r := by omega
    have hc := hcount hq i r hrpos
    have hfirst : 13^(10*j+24*r) ≤ 13^(120*k+68) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have hsecond : 13^(10*j+14*r)*q^20 ≤ 13^(120*k+68) := by
      calc
        13^(10*j+14*r)*q^20 ≤ 13^(10*j+14*r)*13^(40*k+40) :=
          Nat.mul_le_mul_left _ hq20
        _ = 13^(10*j+14*r+(40*k+40)) := (pow_add _ _ _).symm
        _ ≤ 13^(120*k+68) := Nat.pow_le_pow_right (by decide) (by omega)
    calc
      (13^j*lps13ClosedReducedWordCount hq i (2*r))^10*q^34 =
          13^(10*j)*(lps13ClosedReducedWordCount hq i (2*r)^10*q^34) := by
        rw [mul_pow,←pow_mul]; ring
      _ ≤ 13^(10*j)*(D*(13^(24*r)+13^(14*r)*q^20)) := Nat.mul_le_mul_left _ hc
      _ = D*(13^(10*j+24*r)+13^(10*j+14*r)*q^20) := by
        simp only [pow_add]; ring
      _ ≤ D*(13^(120*k+68)+13^(120*k+68)) :=
        Nat.mul_le_mul_left _ (Nat.add_le_add hfirst hsecond)
      _ = (2*D)*13^(120*k+68) := by ring
      _ ≤ (2*D+1)*13^(120*k+68) := Nat.mul_le_mul_right _ (by omega)

def indexSet (m : ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (Finset.range (m+1)).sigma fun j => Finset.range (m-j+1)

theorem indexSet_card (m : ℕ) : (indexSet m).card ≤ (m+1)^2 := by
  rw [indexSet,Finset.card_sigma]
  calc
    ∑ j ∈ Finset.range (m+1), (Finset.range (m-j+1)).card ≤
        ∑ _j ∈ Finset.range (m+1), (m+1) := by
      apply Finset.sum_le_sum
      intro j hj
      simp only [Finset.card_range]
      omega
    _ = (m+1)^2 := by simp [pow_two]

def countSum {q : ℕ} [Fact q.Prime] (hq : 13 < q) (i : LPS13Root q) (m : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (m+1), 13^j*
    ∑ r ∈ Finset.range (m-j+1), lps13ClosedReducedWordCount hq i (2*r)

theorem countSum_pow_bound :
    ∃ D : ℕ, 0 < D ∧ ∀ {q : ℕ} [Fact q.Prime] (hq : 13 < q)
      (i : LPS13Root q) (k : ℕ), q < 13^(2*k+2) →
      countSum hq i (5*k)^10*q^34 ≤ D*(5*k+1)^20*13^(120*k+68) := by
  obtain ⟨D,hD,ht⟩ := term_bound
  refine ⟨D,hD,?_⟩
  intro q hp hq i k hhi
  let f : (Σ _ : ℕ, ℕ) → ℕ := fun z =>
    13^z.1*lps13ClosedReducedWordCount hq i (2*z.2)
  have hs : countSum hq i (5*k)=∑ z ∈ indexSet (5*k), f z := by
    simp only [countSum,indexSet,Finset.sum_sigma,f,Finset.mul_sum]
  have hh := sum_pow_mul_le (indexSet (5*k)) f (q^34) (D*13^(120*k+68)) (by
    intro z hz
    obtain ⟨hj,hr⟩ := Finset.mem_sigma.mp hz
    have hj' := Finset.mem_range.mp hj
    have hr' := Finset.mem_range.mp hr
    exact ht hq i k z.1 z.2 hhi (by omega))
  rw [hs]
  calc
    (∑ z ∈ indexSet (5*k), f z)^10*q^34 ≤ (indexSet (5*k)).card^10*(D*13^(120*k+68)) := hh
    _ ≤ ((5*k+1)^2)^10*(D*13^(120*k+68)) :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (indexSet_card (5*k)) 10)
    _ = D*(5*k+1)^20*13^(120*k+68) := by rw [←pow_mul]; ring

theorem trace_eq_nat {q : ℕ} [Fact q.Prime] (hq : 13 < q) (i : LPS13Root q) (m : ℕ) :
    Matrix.trace ((Polynomial.aeval ((lps13Graph hq i).adjMatrix ℝ)
      (lps13NonbacktrackingPolynomial m))^2) =
      ((Fintype.card (LPS13Vertex q)*countSum hq i m : ℕ) : ℝ) := by
  rw [lps13_squared_trace_eq_closed_reduced_word_count]
  simp [countSum]

theorem trace_nat_pow_bound :
    ∃ D : ℕ, 0 < D ∧ ∀ {q : ℕ} [Fact q.Prime] (hq : 13 < q)
      (i : LPS13Root q) (k : ℕ), 13^(2*k) ≤ q → q < 13^(2*k+2) →
      (Fintype.card (LPS13Vertex q)*countSum hq i (5*k))^10 ≤
        D*(5*k+1)^20*13^(112*k+68) := by
  obtain ⟨D,hD,hS⟩ := countSum_pow_bound
  refine ⟨2^10*D,by positivity,?_⟩
  intro q hp hq i k hlo hhi
  have hc := lps13_vertex_card_le_two_mul_cube (q := q)
  have hb := hS hq i k hhi
  have hq4 : 13^(8*k) ≤ q^4 := by
    convert Nat.pow_le_pow_left hlo 4 using 1 <;> rw [←pow_mul] <;> congr 1 <;> omega
  have hbound : (Fintype.card (LPS13Vertex q)*countSum hq i (5*k))^10*q^4 ≤
      (2^10*D)*(5*k+1)^20*13^(120*k+68) := by
    calc
      (Fintype.card (LPS13Vertex q)*countSum hq i (5*k))^10*q^4 ≤
          ((2*q^3)*countSum hq i (5*k))^10*q^4 :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (Nat.mul_le_mul_right _ hc) 10)
      _ = 2^10*(countSum hq i (5*k)^10*q^34) := by ring
      _ ≤ 2^10*(D*(5*k+1)^20*13^(120*k+68)) := Nat.mul_le_mul_left _ hb
      _ = _ := by ring
  have hsmall := (Nat.mul_le_mul_left
    ((Fintype.card (LPS13Vertex q)*countSum hq i (5*k))^10) hq4).trans hbound
  have he : 13^(120*k+68)=13^(112*k+68)*13^(8*k) := by
    rw [←pow_add]; congr 1; omega
  rw [he,←mul_assoc] at hsmall
  exact Nat.le_of_mul_le_mul_right hsmall (by positivity)

end OPG37364.TraceUpper

namespace OPG37364

theorem _root_.solution :
    ∃ D : ℕ, 0 < D ∧ ∀ {q : ℕ} [Fact q.Prime] (hq : 13 < q)
      (i : LPS13Root q) (k : ℕ), 13^(2*k) ≤ q → q < 13^(2*k+2) →
      (Matrix.trace ((Polynomial.aeval ((lps13Graph hq i).adjMatrix ℝ)
        (lps13NonbacktrackingPolynomial (5*k)))^2))^10 ≤
        (D : ℝ)*(5*k+1)^20*13^(112*k+68) := by
  obtain ⟨D,hD,h⟩ := TraceUpper.trace_nat_pow_bound
  refine ⟨D,hD,?_⟩
  intro q hp hq i k hlo hhi
  rw [TraceUpper.trace_eq_nat]
  exact_mod_cast h hq i k hlo hhi

end OPG37364

end

end Stage17BSource18
