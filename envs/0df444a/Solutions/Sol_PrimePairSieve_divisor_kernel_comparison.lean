-- Prove2me | solution 1 for PrimePairSieve.divisor_kernel_comparison
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-19T22:57:46.177415+00:00
-- url     : https://prove2.me/submissions/a017c903-2924-4190-981a-418df20bf522

import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
open scoped BigOperators

noncomputable section
namespace PrimePairSieve

/-- A genuine finite subset-product sum, with no denominator estimate encoded in its definition. -/
def subsetKernelSum {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (v : ι → ℕ) (F : ℕ → ℝ) : ℝ :=
  ∑ t ∈ s.powerset, (∏ i ∈ t, w i) * F (∏ i ∈ t, v i)

@[simp] theorem subsetKernelSum_empty {ι : Type*} (w : ι → ℝ)
    (v : ι → ℕ) (F : ℕ → ℝ) :
    subsetKernelSum ∅ w v F = F 1 := by
  simp [subsetKernelSum]

private theorem subsetKernelSum_insert {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (i : ι) (hi : i ∉ s) (w : ι → ℝ)
    (v : ι → ℕ) (F : ℕ → ℝ) :
    subsetKernelSum (insert i s) w v F =
      subsetKernelSum s w v F +
        w i * subsetKernelSum s w v (fun n => F (v i * n)) := by
  simp only [subsetKernelSum, Finset.sum_powerset_insert hi]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  have hit : i ∉ t := fun h => hi ((Finset.mem_powerset.mp ht) h)
  simp only [Finset.prod_insert hit]
  ring

private theorem subsetKernelSum_scale_le {ι : Type*}
    (s : Finset ι) (w : ι → ℝ) (v : ι → ℕ) (F : ℕ → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hF : Antitone F)
    (p : ℕ) (hp : 1 ≤ p) :
    subsetKernelSum s w v (fun n => F (p * n)) ≤ subsetKernelSum s w v F := by
  apply Finset.sum_le_sum
  intro t ht
  apply mul_le_mul_of_nonneg_left
  · apply hF
    simpa only [one_mul] using Nat.mul_le_mul_right (∏ i ∈ t, v i) hp
  · exact Finset.prod_nonneg (fun i hi => hw i ((Finset.mem_powerset.mp ht) hi))

/-- Increasing nonnegative local weights decreases the normalized expectation of an
antitone function of the subset product. This is a finite comparison, with all normalizers
cross-multiplied. No positivity hypothesis on the kernel is needed. -/
theorem subsetKernelSum_normalized_antitone {ι : Type*}
    (s : Finset ι) (a b : ι → ℝ) (v : ι → ℕ) (F : ℕ → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hab : ∀ i ∈ s, a i ≤ b i)
    (hv : ∀ i ∈ s, 1 ≤ v i) (hF : Antitone F) :
    subsetKernelSum s b v F * (∏ i ∈ s, (1 + a i)) ≤
      subsetKernelSum s a v F * (∏ i ∈ s, (1 + b i)) := by
  classical
  revert ha hab hv hF
  induction s using Finset.induction_on generalizing F with
  | empty =>
      intro ha hab hv hF
      simp
  | @insert i s hi ih =>
      intro ha hab hv hF
      have hai : 0 ≤ a i := ha i (Finset.mem_insert_self _ _)
      have habi : a i ≤ b i := hab i (Finset.mem_insert_self _ _)
      have hbi : 0 ≤ b i := hai.trans habi
      have hvi : 1 ≤ v i := hv i (Finset.mem_insert_self _ _)
      have has : ∀ j ∈ s, 0 ≤ a j := fun j hj => ha j (Finset.mem_insert_of_mem hj)
      have habs : ∀ j ∈ s, a j ≤ b j := fun j hj => hab j (Finset.mem_insert_of_mem hj)
      have hvs : ∀ j ∈ s, 1 ≤ v j := fun j hj => hv j (Finset.mem_insert_of_mem hj)
      have hFv : Antitone (fun n => F (v i * n)) := by
        intro m n hmn
        exact hF (Nat.mul_le_mul_left (v i) hmn)
      have hmain := ih F has habs hvs hF
      have hshift := ih (fun n => F (v i * n)) has habs hvs hFv
      have hcombined :
          (subsetKernelSum s b v F +
              b i * subsetKernelSum s b v (fun n => F (v i * n))) *
              (∏ j ∈ s, (1 + a j)) ≤
          (subsetKernelSum s a v F +
              b i * subsetKernelSum s a v (fun n => F (v i * n))) *
              (∏ j ∈ s, (1 + b j)) := by
        nlinarith [mul_le_mul_of_nonneg_left hshift hbi]
      have hscale := subsetKernelSum_scale_le s a v F has hF (v i) hvi
      have hlocal :
          (subsetKernelSum s a v F +
              b i * subsetKernelSum s a v (fun n => F (v i * n))) * (1 + a i) ≤
          (subsetKernelSum s a v F +
              a i * subsetKernelSum s a v (fun n => F (v i * n))) * (1 + b i) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr habi) (sub_nonneg.mpr hscale)]
      have hnorm : 0 ≤ ∏ j ∈ s, (1 + b j) :=
        Finset.prod_nonneg (fun j hj => by linarith [has j hj, habs j hj])
      have hcombined' := mul_le_mul_of_nonneg_right hcombined (by linarith : 0 ≤ 1 + a i)
      have hlocal' := mul_le_mul_of_nonneg_right hlocal hnorm
      rw [subsetKernelSum_insert s i hi b v F,
        subsetKernelSum_insert s i hi a v F,
        Finset.prod_insert hi, Finset.prod_insert hi]
      nlinarith

/-- Ordinary sharp cutoff, including zero or negative cutoffs. -/
def cutoffKernel (z : ℝ) (n : ℕ) : ℝ := if (n : ℝ) ≤ z then 1 else 0

/-- The weighted cutoff is defined at z=0 too; it is identically zero there. -/
def weightedCutoffKernel (z : ℝ) (n : ℕ) : ℝ :=
  if (n : ℝ) ≤ z then z / (z + (n : ℝ)) else 0

theorem cutoffKernel_antitone (z : ℝ) : Antitone (cutoffKernel z) := by
  intro m n hmn
  have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
  by_cases hn : (n : ℝ) ≤ z
  · have hm := hmn'.trans hn
    simp [cutoffKernel, hn, hm]
  · simp only [cutoffKernel, if_neg hn]
    split_ifs <;> norm_num

theorem weightedCutoffKernel_antitone (z : ℝ) (hz : 0 ≤ z) :
    Antitone (weightedCutoffKernel z) := by
  by_cases hz0 : z = 0
  · subst z
    intro m n hmn
    simp [weightedCutoffKernel]
  have hzpos : 0 < z := lt_of_le_of_ne hz (Ne.symm hz0)
  intro m n hmn
  have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
  by_cases hn : (n : ℝ) ≤ z
  · have hm := hmn'.trans hn
    simp only [weightedCutoffKernel, if_pos hn, if_pos hm]
    exact div_le_div_of_nonneg_left hz
      (add_pos_of_pos_of_nonneg hzpos (Nat.cast_nonneg m))
      (add_le_add_right hmn' z)
  · simp only [weightedCutoffKernel, if_neg hn]
    split_ifs
    · exact div_nonneg hz (add_nonneg hz (Nat.cast_nonneg _))
    · exact le_rfl

/-- The positive-cutoff expression is exactly the Montgomery weighted kernel. -/
theorem weightedCutoffKernel_eq (z : ℝ) (hz : 0 < z) (n : ℕ) :
    weightedCutoffKernel z n =
      if (n : ℝ) ≤ z then 1 / (1 + (n : ℝ) / z) else 0 := by
  unfold weightedCutoffKernel
  split_ifs
  · have hzn : z + (n : ℝ) ≠ 0 :=
      ne_of_gt (add_pos_of_pos_of_nonneg hz (Nat.cast_nonneg n))
    field_simp [hz.ne', hzn]
    <;> ring
  · rfl

@[simp] theorem weightedCutoffKernel_zero (n : ℕ) : weightedCutoffKernel 0 n = 0 := by
  simp [weightedCutoffKernel]

/-- Products of generators at least one never meet the zero sharp cutoff. -/
theorem subsetKernelSum_cutoff_zero {ι : Type*} (s : Finset ι)
    (w : ι → ℝ) (v : ι → ℕ) (hv : ∀ i ∈ s, 1 ≤ v i) :
    subsetKernelSum s w v (cutoffKernel 0) = 0 := by
  apply Finset.sum_eq_zero
  intro t ht
  have hprod : 1 ≤ ∏ i ∈ t, v i :=
    Finset.one_le_prod' (fun i hi => hv i ((Finset.mem_powerset.mp ht) hi))
  have hpos : (0 : ℝ) < (∏ i ∈ t, v i : ℕ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hprod)
  simp only [cutoffKernel, if_neg (not_le_of_gt hpos), mul_zero]

/-- The prime-local Selberg factor for the actual pair density, on prime inputs and even d. -/
def pairLocalWeight (d p : ℕ) : ℝ :=
  if p ∣ d then 1 / ((p : ℝ) - 1) else 2 / ((p : ℝ) - 2)

/-- The base shift-two factors, written without any natural-divisibility reduction. -/
def basePairLocalWeight (p : ℕ) : ℝ :=
  if p = 2 then 1 else 2 / ((p : ℝ) - 2)

def pairLocalCorrection (d p : ℕ) : ℝ :=
  if 2 < p ∧ p ∣ d then ((p : ℝ) - 1) / ((p : ℝ) - 2) else 1

private theorem pairLocalWeight_comparison (d p : ℕ) (hp : p.Prime) (hd : 2 ∣ d) :
    0 ≤ pairLocalWeight d p ∧
    pairLocalWeight d p ≤ basePairLocalWeight p ∧
    (1 + pairLocalWeight d p) * pairLocalCorrection d p =
      1 + basePairLocalWeight p := by
  by_cases hp2 : p = 2
  · subst p
    norm_num [pairLocalWeight, basePairLocalWeight, pairLocalCorrection, hd]
  have hpgt : 2 < p := by have := hp.two_le; omega
  have hpgt' : (2 : ℝ) < p := by exact_mod_cast hpgt
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hp2' : (0 : ℝ) < (p : ℝ) - 2 := by linarith
  by_cases hpd : p ∣ d
  · simp only [pairLocalWeight, basePairLocalWeight, pairLocalCorrection,
      if_pos hpd, if_neg hp2, hpgt, hpd, and_self, if_true]
    refine ⟨le_of_lt (one_div_pos.mpr hp1), ?_, ?_⟩
    · apply (div_le_div_iff₀ hp1 hp2').mpr
      linarith
    · field_simp [ne_of_gt hp1, ne_of_gt hp2']
      <;> ring
  · simp only [pairLocalWeight, basePairLocalWeight, pairLocalCorrection,
      if_neg hpd, if_neg hp2, hpd, and_false, if_false, mul_one]
    exact ⟨div_nonneg (by norm_num) hp2'.le, le_rfl, trivial⟩

/-- Shift-uniform finite Euler denominator comparison. The prime 2 factor is unchanged;
only odd prime divisors of d contribute to the explicit finite correction product. -/
theorem primePair_kernel_comparison (s : Finset ℕ) (d : ℕ)
    (hs : ∀ p ∈ s, p.Prime) (hd : 2 ∣ d)
    (F : ℕ → ℝ) (hF : Antitone F) :
    subsetKernelSum s basePairLocalWeight (fun p => p) F ≤
      subsetKernelSum s (pairLocalWeight d) (fun p => p) F *
        ∏ p ∈ s, pairLocalCorrection d p := by
  have hlocal := fun p hp => pairLocalWeight_comparison d p (hs p hp) hd
  have ha : ∀ p ∈ s, 0 ≤ pairLocalWeight d p := fun p hp => (hlocal p hp).1
  have hab : ∀ p ∈ s, pairLocalWeight d p ≤ basePairLocalWeight p :=
    fun p hp => (hlocal p hp).2.1
  have hnormpos : 0 < ∏ p ∈ s, (1 + pairLocalWeight d p) :=
    Finset.prod_pos (fun p hp => by linarith [ha p hp])
  have hnorm : (∏ p ∈ s, (1 + basePairLocalWeight p)) =
      (∏ p ∈ s, (1 + pairLocalWeight d p)) *
        (∏ p ∈ s, pairLocalCorrection d p) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro p hp
    exact (hlocal p hp).2.2.symm
  have h := subsetKernelSum_normalized_antitone s (pairLocalWeight d)
    basePairLocalWeight (fun p => p) F ha hab
    (fun p hp => (hs p hp).one_lt.le) hF
  rw [hnorm] at h
  apply (mul_le_mul_iff_of_pos_right hnormpos).mp
  nlinarith

/-- Both denominator kernels share one finite comparison, including cutoff zero. -/
theorem primePair_two_cutoff_comparisons (s : Finset ℕ) (d : ℕ)
    (hs : ∀ p ∈ s, p.Prime) (hd : 2 ∣ d) (z : ℝ) (hz : 0 ≤ z) :
    (subsetKernelSum s basePairLocalWeight (fun p => p) (cutoffKernel z) ≤
      subsetKernelSum s (pairLocalWeight d) (fun p => p) (cutoffKernel z) *
        ∏ p ∈ s, pairLocalCorrection d p) ∧
    (subsetKernelSum s basePairLocalWeight (fun p => p) (weightedCutoffKernel z) ≤
      subsetKernelSum s (pairLocalWeight d) (fun p => p) (weightedCutoffKernel z) *
        ∏ p ∈ s, pairLocalCorrection d p) := by
  exact ⟨primePair_kernel_comparison s d hs hd _ (cutoffKernel_antitone z),
    primePair_kernel_comparison s d hs hd _ (weightedCutoffKernel_antitone z hz)⟩

/-- The finite subset expression is exactly the divisor sum for any multiplicative
arithmetic coefficient on squarefree P, not a separately postulated model. -/
theorem divisorKernelSum_eq_subset (P : ℕ) (hP : Squarefree P)
    (g : ArithmeticFunction ℝ) (hg : g.IsMultiplicative) (F : ℕ → ℝ) :
    (∑ n ∈ P.divisors, g n * F n) =
      subsetKernelSum P.primeFactors (fun p => g p) (fun p => p) F := by
  rw [← Nat.divisors_filter_squarefree_of_squarefree hP,
    Nat.sum_divisors_filter_squarefree hP.ne_zero, Nat.factors_eq]
  unfold subsetKernelSum
  apply Finset.sum_congr rfl
  intro t ht
  rw [t.prod_val, Function.id_def,
    hg.map_prod_of_subset_primeFactors P t (Finset.mem_powerset.mp ht)]

private theorem subsetKernelSum_congr_weights {ι : Type*} (s : Finset ι)
    (a b : ι → ℝ) (v : ι → ℕ) (F : ℕ → ℝ) (hab : ∀ i ∈ s, a i = b i) :
    subsetKernelSum s a v F = subsetKernelSum s b v F := by
  apply Finset.sum_congr rfl
  intro t ht
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  exact hab i ((Finset.mem_powerset.mp ht) hi)

/-- The same comparison over the actual divisor indexing, requiring only multiplicativity
and the explicit prime-local coefficient formulas. These are exactly the obligations
supplied by pairDensity and BoundingSieve.selbergTerms, not the desired sum inequality. -/
theorem primePair_divisorKernel_comparison (P d : ℕ) (hP : Squarefree P)
    (hd : 2 ∣ d) (g₀ g : ArithmeticFunction ℝ)
    (hg₀ : g₀.IsMultiplicative) (hg : g.IsMultiplicative)
    (hbase : ∀ p ∈ P.primeFactors, g₀ p = basePairLocalWeight p)
    (hshift : ∀ p ∈ P.primeFactors, g p = pairLocalWeight d p)
    (F : ℕ → ℝ) (hF : Antitone F) :
    (∑ n ∈ P.divisors, g₀ n * F n) ≤
      (∑ n ∈ P.divisors, g n * F n) *
        ∏ p ∈ P.primeFactors, pairLocalCorrection d p := by
  rw [divisorKernelSum_eq_subset P hP g₀ hg₀ F,
    divisorKernelSum_eq_subset P hP g hg F,
    subsetKernelSum_congr_weights P.primeFactors (fun p => g₀ p)
      basePairLocalWeight (fun p => p) F hbase,
    subsetKernelSum_congr_weights P.primeFactors (fun p => g p)
      (pairLocalWeight d) (fun p => p) F hshift]
  exact primePair_kernel_comparison P.primeFactors d
    (fun p hp => Nat.prime_of_mem_primeFactors hp) hd F hF

end PrimePairSieve



/-- Exact inline public proposition, with the coefficient functions discharged. -/
theorem solution (P d : ℕ) (hP : Squarefree P) (hd : 2 ∣ d)
    (F : ℕ → ℝ) (hF : Antitone F) :
    (∑ n ∈ P.divisors,
      (∏ p ∈ n.primeFactors,
        if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)) * F n) ≤
    (∑ n ∈ P.divisors,
      (∏ p ∈ n.primeFactors,
        if p ∣ d then (1 : ℝ) / ((p : ℝ) - 1) else 2 / ((p : ℝ) - 2)) * F n) *
      ∏ p ∈ P.primeFactors,
        if 2 < p ∧ p ∣ d then ((p : ℝ) - 1) / ((p : ℝ) - 2) else 1 := by
  let g₀ : ArithmeticFunction ℝ :=
    ArithmeticFunction.prodPrimeFactors PrimePairSieve.basePairLocalWeight
  let g : ArithmeticFunction ℝ :=
    ArithmeticFunction.prodPrimeFactors (PrimePairSieve.pairLocalWeight d)
  have hg₀ : g₀.IsMultiplicative := ArithmeticFunction.IsMultiplicative.prodPrimeFactors _
  have hg : g.IsMultiplicative := ArithmeticFunction.IsMultiplicative.prodPrimeFactors _
  have hbase : ∀ p ∈ P.primeFactors, g₀ p = PrimePairSieve.basePairLocalWeight p := by
    intro p hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    simp only [g₀, ArithmeticFunction.prodPrimeFactors_apply hprime.ne_zero,
      hprime.primeFactors, Finset.prod_singleton]
  have hshift : ∀ p ∈ P.primeFactors, g p = PrimePairSieve.pairLocalWeight d p := by
    intro p hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    simp only [g, ArithmeticFunction.prodPrimeFactors_apply hprime.ne_zero,
      hprime.primeFactors, Finset.prod_singleton]
  have h := PrimePairSieve.primePair_divisorKernel_comparison P d hP hd
    g₀ g hg₀ hg hbase hshift F hF
  have hsum₀ : (∑ n ∈ P.divisors, g₀ n * F n) =
      ∑ n ∈ P.divisors,
        (∏ p ∈ n.primeFactors, PrimePairSieve.basePairLocalWeight p) * F n := by
    apply Finset.sum_congr rfl
    intro n hn
    have hn0 : n ≠ 0 := ne_zero_of_dvd_ne_zero hP.ne_zero (Nat.dvd_of_mem_divisors hn)
    simp only [g₀, ArithmeticFunction.prodPrimeFactors_apply hn0]
  have hsum : (∑ n ∈ P.divisors, g n * F n) =
      ∑ n ∈ P.divisors,
        (∏ p ∈ n.primeFactors, PrimePairSieve.pairLocalWeight d p) * F n := by
    apply Finset.sum_congr rfl
    intro n hn
    have hn0 : n ≠ 0 := ne_zero_of_dvd_ne_zero hP.ne_zero (Nat.dvd_of_mem_divisors hn)
    simp only [g, ArithmeticFunction.prodPrimeFactors_apply hn0]
  rw [hsum₀, hsum] at h
  simpa only [PrimePairSieve.basePairLocalWeight, PrimePairSieve.pairLocalWeight,
    PrimePairSieve.pairLocalCorrection] using h

#print axioms solution
