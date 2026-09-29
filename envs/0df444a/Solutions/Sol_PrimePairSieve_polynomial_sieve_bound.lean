-- Prove2me | solution 1 for PrimePairSieve.polynomial_sieve_bound
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-19T22:35:24.028528+00:00
-- url     : https://prove2.me/submissions/dba95c0e-9ed4-453b-ac69-f6a95c60ca99

import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega
open scoped BigOperators

set_option autoImplicit false
open scoped BigOperators

namespace PrimePairSieve

/-- The actual bad residue classes of the polynomial `n(n+d)` modulo `m`.
This definition assumes neither squarefreeness nor a formula for the root count. -/
def pairResidues (m d : ℕ) : Finset ℕ :=
  (Finset.range m).filter (fun r => m ∣ r * (r + d))

private theorem periodic_count_split (P : ℕ → Prop) [DecidablePred P]
    (m N : ℕ) (hperiod : ∀ n, P (n + m) ↔ P n) :
    ((Finset.range N).filter P).card =
      (N / m) * ((Finset.range m).filter P).card +
        ((Finset.range (N % m)).filter P).card := by
  let f : ℕ → ℕ := fun n => if P n then 1 else 0
  have hf (n : ℕ) : f (n + m) = f n := by
    simp only [f, hperiod n]
  have hshift (q n : ℕ) : f (q * m + n) = f n := by
    induction q with
    | zero => simp only [Nat.zero_mul, zero_add]
    | succ q ih =>
      calc
        f ((q + 1) * m + n) = f ((q * m + n) + m) := by
          congr 1
          ring
        _ = f (q * m + n) := hf _
        _ = f n := ih
  have hblocks (q : ℕ) :
      (∑ n ∈ Finset.range (q * m), f n) = q * ∑ n ∈ Finset.range m, f n := by
    induction q with
    | zero => simp
    | succ q ih =>
      rw [Nat.succ_mul, Finset.sum_range_add, ih]
      simp_rw [hshift]
      ring
  have hN : (N / m) * m + N % m = N := by
    simpa only [Nat.mul_comm] using Nat.div_add_mod N m
  have hsum : (∑ n ∈ Finset.range N, f n) =
      (N / m) * (∑ n ∈ Finset.range m, f n) +
        ∑ n ∈ Finset.range (N % m), f n := by
    calc
      _ = ∑ n ∈ Finset.range ((N / m) * m + N % m), f n := by rw [hN]
      _ = _ := by
        rw [Finset.sum_range_add, hblocks]
        simp_rw [hshift]
  simpa only [Finset.card_eq_sum_ones, Finset.sum_filter, f] using hsum

/-- Every periodic residue condition has remainder at most one complete period's count.
No distribution or sieving estimate is assumed. -/
theorem periodic_count_remainder (P : ℕ → Prop) [DecidablePred P]
    (m N : ℕ) (hm : 0 < m) (hperiod : ∀ n, P (n + m) ↔ P n) :
    |(((Finset.range N).filter P).card : ℝ) -
        (N : ℝ) * (((Finset.range m).filter P).card : ℝ) / (m : ℝ)| ≤
      (((Finset.range m).filter P).card : ℝ) := by
  let A := ((Finset.range N).filter P).card
  let B := ((Finset.range m).filter P).card
  let R := ((Finset.range (N % m)).filter P).card
  let q := N / m
  let r := N % m
  have hA : A = q * B + R := periodic_count_split P m N hperiod
  have hN : q * m + r = N := by
    simpa only [Nat.mul_comm] using Nat.div_add_mod N m
  have hr : r < m := Nat.mod_lt N hm
  have hR : R ≤ B := by
    apply Finset.card_le_card
    exact Finset.filter_subset_filter P (Finset.range_mono hr.le)
  have hAR : (A : ℝ) = (q : ℝ) * (B : ℝ) + (R : ℝ) := by exact_mod_cast hA
  have hNR : (q : ℝ) * (m : ℝ) + (r : ℝ) = (N : ℝ) := by exact_mod_cast hN
  have hRR : (R : ℝ) ≤ (B : ℝ) := by exact_mod_cast hR
  have hrR : (r : ℝ) ≤ (m : ℝ) := by exact_mod_cast hr.le
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hB0 : (0 : ℝ) ≤ B := Nat.cast_nonneg B
  have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg R
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hmainLo : (q : ℝ) * (B : ℝ) ≤ (N : ℝ) * (B : ℝ) / (m : ℝ) := by
    apply (le_div_iff₀ hmR).mpr
    have hprod := congrArg (fun y : ℝ => y * (B : ℝ)) hNR
    nlinarith [mul_nonneg hr0 hB0]
  have hmainHi : (N : ℝ) * (B : ℝ) / (m : ℝ) ≤
      ((q : ℝ) + 1) * (B : ℝ) := by
    apply (div_le_iff₀ hmR).mpr
    have hprod := congrArg (fun y : ℝ => y * (B : ℝ)) hNR
    nlinarith [mul_le_mul_of_nonneg_right hrR hB0]
  change |(A : ℝ) - (N : ℝ) * (B : ℝ) / (m : ℝ)| ≤ (B : ℝ)
  rw [abs_le]
  constructor <;> nlinarith

/-- Exact finite residue distribution for the prime-pair sieve polynomial.
For a squarefree sieve divisor this supplies the genuine arithmetic remainder
`|R_m| ≤ ρ_d(m)`, where `ρ_d(m)` is the number of roots modulo `m`. -/
theorem pair_divisibility_remainder (m d N : ℕ) (hm : 0 < m) :
    |(((Finset.range N).filter (fun n => m ∣ n * (n + d))).card : ℝ) -
        (N : ℝ) * ((pairResidues m d).card : ℝ) / (m : ℝ)| ≤
      ((pairResidues m d).card : ℝ) := by
  apply periodic_count_remainder (fun n => m ∣ n * (n + d)) m N hm
  intro n
  simp only [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mul_mod,
    Nat.mod_self, add_zero, Nat.mod_mod]

end PrimePairSieve



set_option autoImplicit false

namespace PrimePairSieve

/- Shared concrete residue set from the first component. -/
-- Exact shared pairResidues definition appears in the first component.

/-- The polynomial zero locus, with its actual elements rather than a prescribed cardinality. -/
abbrev PairRoots (m d : ℕ) := {z : ZMod m // z * (z + (d : ZMod m)) = 0}

/-- Canonical residues identify the finite natural root set with the modular zero locus. -/
noncomputable def pairResiduesEquivRoots (m d : ℕ) (hm : 0 < m) :
    {r : ℕ // r ∈ pairResidues m d} ≃ PairRoots m d := by
  letI : NeZero m := ⟨hm.ne'⟩
  refine
    { toFun := fun r => ⟨(r.val : ZMod m), ?_⟩
      invFun := fun z => ⟨z.val.val, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have hdiv := (Finset.mem_filter.mp r.property).2
    simpa only [Nat.cast_mul, Nat.cast_add] using
      (ZMod.natCast_eq_zero_iff (r.val * (r.val + d)) m).mpr hdiv
  · refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr z.val.val_lt, ?_⟩
    apply (ZMod.natCast_eq_zero_iff (z.val.val * (z.val.val + d)) m).mp
    simpa only [Nat.cast_mul, Nat.cast_add, ZMod.natCast_zmod_val] using z.property
  · intro r
    apply Subtype.ext
    exact ZMod.val_natCast_of_lt
      (Finset.mem_range.mp (Finset.mem_filter.mp r.property).1)
  · intro z
    apply Subtype.ext
    exact ZMod.natCast_zmod_val z.val

theorem pairResidues_card_eq_roots (m d : ℕ) (hm : 0 < m) :
    (pairResidues m d).card = Nat.card (PairRoots m d) := by
  calc
    _ = Nat.card {r : ℕ // r ∈ pairResidues m d} := by
      simp only [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ = _ := Nat.card_congr (pairResiduesEquivRoots m d hm)

/-- CRT transports the literal polynomial zero locus to the product of the two zero loci. -/
noncomputable def pairRootsCRT (m n d : ℕ) (hcop : m.Coprime n) :
    PairRoots (m * n) d ≃ PairRoots m d × PairRoots n d := by
  let e := ZMod.chineseRemainder hcop
  let e1 : PairRoots (m * n) d ≃
      {w : ZMod m × ZMod n // w * (w + (d : ZMod m × ZMod n)) = 0} :=
    e.toEquiv.subtypeEquiv (by
      intro z
      constructor
      · intro hz
        have h := congrArg e hz
        simpa only [RingEquiv.toEquiv_eq_coe, RingEquiv.coe_toEquiv, map_mul, map_add, map_natCast, map_zero] using h
      · intro hz
        apply e.injective
        simpa only [RingEquiv.toEquiv_eq_coe, RingEquiv.coe_toEquiv, map_mul, map_add, map_natCast, map_zero] using hz)
  let e2 : {w : ZMod m × ZMod n // w * (w + (d : ZMod m × ZMod n)) = 0} ≃
      PairRoots m d × PairRoots n d :=
    { toFun := fun w =>
        (⟨w.val.1, congrArg Prod.fst w.property⟩,
         ⟨w.val.2, congrArg Prod.snd w.property⟩)
      invFun := fun w => ⟨(w.1.val, w.2.val), Prod.ext w.1.property w.2.property⟩
      left_inv := by rintro ⟨⟨u, v⟩, h⟩; rfl
      right_inv := by rintro ⟨⟨u, hu⟩, ⟨v, hv⟩⟩; rfl }
  exact e1.trans e2

/-- The actual root count is multiplicative for coprime moduli, including zero and one. -/
theorem pairResidues_card_mul (m n d : ℕ) (hcop : m.Coprime n) :
    (pairResidues (m * n) d).card =
      (pairResidues m d).card * (pairResidues n d).card := by
  by_cases hm : m = 0
  · subst m
    simp [pairResidues]
  by_cases hn : n = 0
  · subst n
    simp [pairResidues]
  have hm0 : 0 < m := Nat.pos_of_ne_zero hm
  have hn0 : 0 < n := Nat.pos_of_ne_zero hn
  calc
    _ = Nat.card (PairRoots (m * n) d) := pairResidues_card_eq_roots _ _ (Nat.mul_pos hm0 hn0)
    _ = Nat.card (PairRoots m d × PairRoots n d) := Nat.card_congr (pairRootsCRT m n d hcop)
    _ = Nat.card (PairRoots m d) * Nat.card (PairRoots n d) := Nat.card_prod _ _
    _ = _ := by rw [← pairResidues_card_eq_roots m d hm0, ← pairResidues_card_eq_roots n d hn0]

@[simp] theorem pairResidues_card_one (d : ℕ) : (pairResidues 1 d).card = 1 := by
  simp [pairResidues]

/-- A prime modulus has exactly the roots `0` and `−d`; they merge iff the prime divides `d`. -/
theorem pairResidues_card_prime (p d : ℕ) (hp : p.Prime) :
    (pairResidues p d).card = if p ∣ d then 1 else 2 := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  have hroots : (Finset.univ.filter
      (fun z : ZMod p => z * (z + (d : ZMod p)) = 0)) =
      ({0, -(d : ZMod p)} : Finset (ZMod p)) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, mul_eq_zero, add_eq_zero_iff_eq_neg]
  rw [pairResidues_card_eq_roots p d hp.pos]
  change Nat.card {z : ZMod p // z * (z + (d : ZMod p)) = 0} = _
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, hroots]
  by_cases hpd : p ∣ d
  · have hd : (d : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff d p).mpr hpd
    simp [hpd, hd]
  · have hd : (d : ZMod p) ≠ 0 := fun h => hpd ((ZMod.natCast_eq_zero_iff d p).mp h)
    have hne : (0 : ZMod p) ≠ -(d : ZMod p) := fun h => hd (neg_eq_zero.mp h.symm)
    rw [if_neg hpd, Finset.card_pair hne]

/-- Actual root cardinalities, cast to an arithmetic function; the zero modulus has no natural residues. -/
noncomputable def pairRootCount (d : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun m => ((pairResidues m d).card : ℝ), by simp [pairResidues]⟩

@[simp] theorem pairRootCount_apply (d m : ℕ) :
    pairRootCount d m = ((pairResidues m d).card : ℝ) := rfl

theorem pairRootCount_isMultiplicative (d : ℕ) : (pairRootCount d).IsMultiplicative := by
  refine ⟨by simp, ?_⟩
  intro m n hcop
  simp only [pairRootCount_apply, pairResidues_card_mul m n d hcop, Nat.cast_mul]

/-- The genuine divisibility density `ρ_d(m)/m`. -/
noncomputable def pairDensity (d : ℕ) : ArithmeticFunction ℝ :=
  (pairRootCount d).pdiv (ArithmeticFunction.id : ArithmeticFunction ℝ)

@[simp] theorem pairDensity_apply (d m : ℕ) :
    pairDensity d m = ((pairResidues m d).card : ℝ) / (m : ℝ) := by
  simp [pairDensity]

theorem pairDensity_isMultiplicative (d : ℕ) : (pairDensity d).IsMultiplicative :=
  (pairRootCount_isMultiplicative d).pdiv ArithmeticFunction.isMultiplicative_id.natCast

theorem pairDensity_prime (p d : ℕ) (hp : p.Prime) :
    pairDensity d p = if p ∣ d then 1 / (p : ℝ) else 2 / (p : ℝ) := by
  by_cases hpd : p ∣ d <;> simp [pairDensity_apply, pairResidues_card_prime p d hp, hpd]

/-- For the target's even shift every prime density is strictly between zero and one.
In particular the prime `2` uses the one-root branch. -/
theorem pairDensity_prime_bounds (p d : ℕ) (hp : p.Prime) (hd : 2 ∣ d) :
    0 < pairDensity d p ∧ pairDensity d p < 1 := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  rw [pairDensity_prime p d hp]
  by_cases hpd : p ∣ d
  · rw [if_pos hpd]
    refine ⟨by positivity, (div_lt_one hpR).mpr ?_⟩
    exact_mod_cast hp.one_lt
  · rw [if_neg hpd]
    have hp2 : 2 < p := by
      have hne : p ≠ 2 := by
        intro h
        apply hpd
        simpa only [h] using hd
      have hge := hp.two_le
      omega
    refine ⟨by positivity, (div_lt_one hpR).mpr ?_⟩
    exact_mod_cast hp2

end PrimePairSieve


namespace PrimePairSieve

/-- Strict growth preserves argument multiplicity when the polynomial values are stored in a Finset. -/
theorem pairPolynomial_strictMono (d : ℕ) (hd : 0 < d) :
    StrictMono (fun n : ℕ => n * (n + d)) := by
  intro a b hab
  calc
    a * (a + d) ≤ a * (b + d) := Nat.mul_le_mul_left a (Nat.add_le_add_right hab.le d)
    _ < b * (b + d) := Nat.mul_lt_mul_of_pos_right hab (by omega)

/-- The actual polynomial-image sieve; all density properties come from the root count and CRT. -/
noncomputable def primePairBoundingSieve (N d P : ℕ) (hd0 : 0 < d)
    (hd2 : 2 ∣ d) (hP : Squarefree P) : BoundingSieve where
  support := (Finset.range N).image (fun n => n * (n + d))
  prodPrimes := P
  prodPrimes_squarefree := hP
  weights := fun _ => 1
  weights_nonneg := fun _ => by norm_num
  totalMass := (N : ℝ)
  nu := pairDensity d
  nu_mult := pairDensity_isMultiplicative d
  nu_pos_of_prime := fun p hp _ => (pairDensity_prime_bounds p d hp hd2).1
  nu_lt_one_of_prime := fun p hp _ => (pairDensity_prime_bounds p d hp hd2).2

private theorem polynomial_image_indicator_count (N d : ℕ) (hd0 : 0 < d)
    (Q : ℕ → Prop) [DecidablePred Q] :
    (∑ y ∈ (Finset.range N).image (fun n => n * (n + d)),
      if Q y then (1 : ℝ) else 0) =
      (((Finset.range N).filter (fun n => Q (n * (n + d)))).card : ℝ) := by
  rw [Finset.sum_image]
  · rw [Finset.card_eq_sum_ones]
    push_cast
    rw [Finset.sum_filter]
  · intro a _ b _ h
    exact (pairPolynomial_strictMono d hd0).injective h

/-- Exact divisor counts in the sieve support are counts of polynomial roots in the original interval. -/
theorem primePair_multSum (N d P : ℕ) (hd0 : 0 < d)
    (hd2 : 2 ∣ d) (hP : Squarefree P) (m : ℕ) :
    (primePairBoundingSieve N d P hd0 hd2 hP).multSum m =
      (((Finset.range N).filter (fun n => m ∣ n * (n + d))).card : ℝ) := by
  change (∑ y ∈ (Finset.range N).image (fun n => n * (n + d)),
    if m ∣ y then (1 : ℝ) else 0) = _
  exact polynomial_image_indicator_count N d hd0 (fun y => m ∣ y)

/-- The concrete sieve remainder costs at most the number of roots modulo the divisor. -/
theorem primePair_rem_bound (N d P : ℕ) (hd0 : 0 < d)
    (hd2 : 2 ∣ d) (hP : Squarefree P) (m : ℕ) (hm : 0 < m) :
    |(primePairBoundingSieve N d P hd0 hd2 hP).rem m| ≤
      ((pairResidues m d).card : ℝ) := by
  rw [BoundingSieve.rem, primePair_multSum]
  change |(((Finset.range N).filter (fun n => m ∣ n * (n + d))).card : ℝ) -
    pairDensity d m * (N : ℝ)| ≤ _
  have hmain : pairDensity d m * (N : ℝ) =
      (N : ℝ) * ((pairResidues m d).card : ℝ) / (m : ℝ) := by
    rw [pairDensity_apply]
    ring
  rw [hmain]
  exact pair_divisibility_remainder m d N hm

/-- Sifting the polynomial image is exactly the original interval's coprime-polynomial count. -/
theorem primePair_siftedSum (N d P : ℕ) (hd0 : 0 < d)
    (hd2 : 2 ∣ d) (hP : Squarefree P) :
    (primePairBoundingSieve N d P hd0 hd2 hP).siftedSum =
      (((Finset.range N).filter (fun n => P.Coprime (n * (n + d)))).card : ℝ) := by
  change (∑ y ∈ (Finset.range N).image (fun n => n * (n + d)),
    if P.Coprime y then (1 : ℝ) else 0) = _
  exact polynomial_image_indicator_count N d hd0 (fun y => P.Coprime y)

/-- A concrete prime-pair polynomial sieve inequality with all arithmetic remainders discharged.
The remaining choice and optimization of weights is exposed explicitly. -/
theorem primePair_lambdaSquared_bound (N d P : ℕ) (hd0 : 0 < d)
    (hd2 : 2 ∣ d) (hP : Squarefree P) (w : ℕ → ℝ) (hw : w 1 = 1) :
    (((Finset.range N).filter (fun n => P.Coprime (n * (n + d)))).card : ℝ) ≤
      (N : ℝ) * (∑ m ∈ P.divisors, BoundingSieve.lambdaSquared w m * pairDensity d m) +
        ∑ m ∈ P.divisors,
          |BoundingSieve.lambdaSquared w m| * ((pairResidues m d).card : ℝ) := by
  let s := primePairBoundingSieve N d P hd0 hd2 hP
  have hs := BoundingSieve.siftedSum_le_mainSum_errSum_of_upperMoebius
    (s := s) (BoundingSieve.lambdaSquared w) (BoundingSieve.upperMoebius_lambdaSquared w hw)
  calc
    _ = s.siftedSum := (primePair_siftedSum N d P hd0 hd2 hP).symm
    _ ≤ s.totalMass * s.mainSum (BoundingSieve.lambdaSquared w) +
        s.errSum (BoundingSieve.lambdaSquared w) := hs
    _ ≤ _ := by
      change (N : ℝ) * (∑ m ∈ P.divisors,
          BoundingSieve.lambdaSquared w m * pairDensity d m) +
        (∑ m ∈ P.divisors,
          |BoundingSieve.lambdaSquared w m| * |s.rem m|) ≤ _
      apply add_le_add le_rfl
      apply Finset.sum_le_sum
      intro m hm
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      have hm0 : 0 < m := Nat.pos_of_ne_zero
        (ne_zero_of_dvd_ne_zero hP.ne_zero (Nat.dvd_of_mem_divisors hm))
      exact primePair_rem_bound N d P hd0 hd2 hP m hm0

end PrimePairSieve



theorem solution
    (N d P : ℕ) (hd0 : 0 < d) (hd2 : 2 ∣ d) (hP : Squarefree P)
    (w : ℕ → ℝ) (hw : w 1 = 1) :
    (((Finset.range N).filter (fun n => P.Coprime (n * (n + d)))).card : ℝ) ≤
      (N : ℝ) * (∑ m ∈ P.divisors, BoundingSieve.lambdaSquared w m *
        (((Finset.range m).filter (fun r => m ∣ r * (r + d))).card : ℝ) / (m : ℝ)) +
        ∑ m ∈ P.divisors, |BoundingSieve.lambdaSquared w m| *
          (((Finset.range m).filter (fun r => m ∣ r * (r + d))).card : ℝ) := by
  simpa only [PrimePairSieve.pairDensity_apply, PrimePairSieve.pairResidues, mul_div_assoc]
    using PrimePairSieve.primePair_lambdaSquared_bound N d P hd0 hd2 hP w hw

#print axioms solution
