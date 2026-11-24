-- Prove2me | solution 1 for PaleyWeil.splitLCoeff_newton
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-11-24T17:43:15.386461+00:00
-- url     : https://prove2.me/submissions/fd7ed42d-a616-490c-bdde-f44ae0798866

import Definitions.Def_Sensitivity214439_Phase0_RiemannHypothesisCurves_EulerNewtonIdentity
import Definitions.Def_Sensitivity214439_Phase0_RiemannHypothesisCurves_SplitEulerRecurrence
import Definitions.Def_Sensitivity214439_Phase0_RiemannHypothesisCurves_SplitLSeriesDefs
import Definitions.Def_Sensitivity214439_Phase0_RiemannHypothesisCurves_SplitQuadraticWeight
import Definitions.Def_Sensitivity214439_Phase0_RiemannHypothesisCurves_WeightedGeometricSeries
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Data.Finsupp.Weight
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.UniqueFactorizationDomain.Finsupp
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Theorems.Thm_PaleyWeil_coeff_finite_weightedEuler

namespace Finset
end Finset
namespace PaleyWeil
end PaleyWeil
namespace Polynomial
end Polynomial
namespace PowerSeries
end PowerSeries
namespace UniqueFactorizationMonoid
end UniqueFactorizationMonoid

section


open Polynomial Finset

namespace PaleyWeil



@[simp]
theorem splitQuadraticWeight_one {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (s : Finset K) : splitQuadraticWeight s (1 : K[X]) = 1 := by
  simp [splitQuadraticWeight]

theorem splitQuadraticWeight_mul {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (s : Finset K) {P Q : K[X]} (hP : P ≠ 0) (hQ : Q ≠ 0) :
    splitQuadraticWeight s (P * Q) = splitQuadraticWeight s P * splitQuadraticWeight s Q := by
  unfold splitQuadraticWeight
  rw [natDegree_mul hP hQ, Nat.mul_add, pow_add]
  simp only [eval_mul, Finset.prod_mul_distrib]
  rw [show (-1 : K) ^ (s.card * P.natDegree) * (-1) ^ (s.card * Q.natDegree) *
      ((∏ a ∈ s, P.eval a) * ∏ a ∈ s, Q.eval a) =
      ((-1) ^ (s.card * P.natDegree) * ∏ a ∈ s, P.eval a) *
      ((-1) ^ (s.card * Q.natDegree) * ∏ a ∈ s, Q.eval a) by ring]
  exact map_mul (quadraticChar K) _ _






end PaleyWeil

end

section


open Polynomial Finset

namespace PaleyWeil





@[simp]
theorem splitLCoeff_zero {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (s : Finset K) : splitLCoeff s 0 = 1 := by
  classical
  let oneP : {P : K[X] // IsMonicOfDegree P 0} := ⟨1, by simp⟩
  have hP (P : {P : K[X] // IsMonicOfDegree P 0}) : P = oneP := by
    apply Subtype.ext
    exact isMonicOfDegree_zero_iff.mp P.2
  unfold splitLCoeff
  rw [tsum_eq_single oneP (fun P hne ↦ (hne (hP P)).elim)]
  exact splitQuadraticWeight_one s








end PaleyWeil

end

section


/-!
The unique-factorization and finite Euler-product bridge for the split
quadratic-character L-series. All factorization statements concern actual
monic polynomials; no character-sum estimate is assumed here.
-/

open Polynomial Finset UniqueFactorizationMonoid

namespace PaleyWeil

noncomputable section

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]





























theorem splitQuadraticWeight_pow (s : Finset K) {P : K[X]} (hP : P ≠ 0) (e : ℕ) :
    splitQuadraticWeight s (P ^ e) = splitQuadraticWeight s P ^ e := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [pow_succ, splitQuadraticWeight_mul s (pow_ne_zero _ hP) hP, ih, pow_succ]

theorem splitQuadraticWeight_primeProduct (s : Finset K) (m : MonicPrime K →₀ ℕ) :
    splitQuadraticWeight s (primeProduct m) =
      m.prod (fun P e ↦ splitQuadraticWeight s P ^ e) := by
  classical
  induction m using Finsupp.induction with
  | zero => simp
  | single_add P e m _ _ ih =>
    rw [primeProduct_add, splitQuadraticWeight_mul s (primeProduct_monic _).ne_zero
      (primeProduct_monic _).ne_zero, primeProduct_single,
      splitQuadraticWeight_pow s P.2.1.ne_zero, ih,
      Finsupp.prod_add_index' (fun _ ↦ pow_zero _) (fun _ _ _ ↦ pow_add ..)]
    rw [Finsupp.prod_single_index
      (h := fun (Q : MonicPrime K) (k : ℕ) ↦ splitQuadraticWeight s Q ^ k)
      (pow_zero _)]





theorem splitLCoeff_eq_primeWeights (s : Finset K) (n : ℕ) :
    splitLCoeff s n =
      ∑' m : {m : MonicPrime K →₀ ℕ // primeDegree m = n},
        m.1.prod (fun P e ↦ splitQuadraticWeight s P ^ e) := by
  unfold splitLCoeff
  rw [← (monicDegreeFactorizationEquiv (K := K) n).tsum_eq]
  apply tsum_congr
  intro P
  change splitQuadraticWeight s (P : K[X]) =
    (primeFactors (P : K[X])).prod (fun Q e ↦ splitQuadraticWeight s Q ^ e)
  rw [← splitQuadraticWeight_primeProduct, primeProduct_primeFactors P.2.monic]









@[simp] theorem mem_primesUpTo (n : ℕ) (P : MonicPrime K) :
    P ∈ primesUpTo n ↔ (P : K[X]).natDegree ≤ n := by
  classical
  simp [primesUpTo, Nat.lt_succ_iff]

theorem prime_degree_pos (P : MonicPrime K) : 0 < (P : K[X]).natDegree :=
  P.2.2.natDegree_pos







end
end PaleyWeil

end

section


/-! Weighted geometric factors and their exact formal logarithmic derivatives. -/

open scoped PowerSeries
open PowerSeries Finset

namespace PaleyWeil

noncomputable section



@[simp] theorem coeff_weightedGeometric (w : ℤ) (d n : ℕ) :
    PowerSeries.coeff n (weightedGeometric w d) =
      if d ∣ n then w ^ (n / d) else 0 := by
  simp only [weightedGeometric, coeff_mk]



theorem weightedGeometric_eq_subst (w : ℤ) {d : ℕ} (hd : d ≠ 0) :
    weightedGeometric w d =
      PowerSeries.subst (PowerSeries.X ^ d : ℤ⟦X⟧)
        (PowerSeries.rescale w (PowerSeries.mk 1)) := by
  ext n
  rw [coeff_weightedGeometric, coeff_subst_X_pow hd, coeff_rescale, coeff_mk]
  simp

theorem weightedGeometric_mul (w : ℤ) {d : ℕ} (hd : d ≠ 0) :
    weightedGeometric w d * (1 - PowerSeries.C w * PowerSeries.X ^ d) = 1 := by
  have hbase : (PowerSeries.rescale w (PowerSeries.mk 1)) *
      (1 - PowerSeries.C w * PowerSeries.X) = (1 : ℤ⟦X⟧) := by
    simpa only [map_mul, map_sub, map_one, PowerSeries.rescale_X] using
      congrArg (PowerSeries.rescale w) (PowerSeries.mk_one_mul_one_sub_eq_one ℤ)
  have h := congrArg (PowerSeries.substAlgHom
    (PowerSeries.HasSubst.X_pow (R := ℤ) hd)) hbase
  rw [weightedGeometric_eq_subst w hd]
  simp only [map_mul, map_sub, map_one, PowerSeries.coe_substAlgHom,
    PowerSeries.subst_C,
    PowerSeries.subst_X (PowerSeries.HasSubst.X_pow (R := ℤ) hd)] at h
  simpa only [PowerSeries.C] using h



theorem coeff_weightedPrimeRate (w : ℤ) (d n : ℕ) :
    PowerSeries.coeff n (weightedPrimeRate w d) =
      if d ∣ n ∧ n ≠ 0 then (d : ℤ) * w ^ (n / d) else 0 := by
  simp only [weightedPrimeRate, coeff_C_mul, map_sub, coeff_weightedGeometric, coeff_one]
  by_cases hn : n = 0
  · subst n
    simp
  · by_cases hdn : d ∣ n <;> simp [hn, hdn]

theorem weightedGeometric_logDerivative (w : ℤ) {d : ℕ} (hd : d ≠ 0) :
    PowerSeries.X * PowerSeries.derivative (R := ℤ) (weightedGeometric w d) =
      weightedPrimeRate w d * weightedGeometric w d := by
  let G := weightedGeometric w d
  let A : ℤ⟦X⟧ := PowerSeries.C w * PowerSeries.X ^ d
  have hG : G * (1 - A) = 1 := weightedGeometric_mul w hd
  have hD : PowerSeries.derivative (R := ℤ) G * (1 - A) =
      G * PowerSeries.derivative (R := ℤ) A := by
    have h := congrArg (PowerSeries.derivative (R := ℤ)) hG
    simp only [Derivation.leibniz, smul_eq_mul, map_sub,
      Derivation.map_one_eq_zero, zero_sub] at h
    linear_combination h
  have hA : PowerSeries.X * PowerSeries.derivative (R := ℤ) A =
      PowerSeries.C (d : ℤ) * A := by
    obtain ⟨e, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd
    simp only [A, Derivation.leibniz, smul_eq_mul, PowerSeries.derivative_C,
      PowerSeries.derivative_pow, PowerSeries.derivative_X, mul_one,
      Nat.succ_sub_one, mul_zero, zero_add]
    rw [map_natCast, pow_succ]
    ring
  have hGA : G - 1 = A * G := by
    linear_combination hG
  change PowerSeries.X * PowerSeries.derivative (R := ℤ) G =
    PowerSeries.C (d : ℤ) * (G - 1) * G
  calc
    PowerSeries.X * PowerSeries.derivative (R := ℤ) G =
        (PowerSeries.X * PowerSeries.derivative (R := ℤ) G) * (G * (1 - A)) := by
      rw [hG, mul_one]
    _ = (PowerSeries.X * G) * (PowerSeries.derivative (R := ℤ) G * (1 - A)) := by ring
    _ = (PowerSeries.X * G) * (G * PowerSeries.derivative (R := ℤ) A) := by rw [hD]
    _ = (PowerSeries.X * PowerSeries.derivative (R := ℤ) A) * G ^ 2 := by ring
    _ = PowerSeries.C (d : ℤ) * (G - 1) * G := by rw [hA, hGA]; ring

theorem finite_weightedEuler_logDerivative {ι : Type*}
    (w : ι → ℤ) (d : ι → ℕ) (S : Finset ι) (hd : ∀ i ∈ S, d i ≠ 0) :
    PowerSeries.X * PowerSeries.derivative (R := ℤ)
        (∏ i ∈ S, weightedGeometric (w i) (d i)) =
      (∑ i ∈ S, weightedPrimeRate (w i) (d i)) *
        ∏ i ∈ S, weightedGeometric (w i) (d i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    have hga := weightedGeometric_logDerivative (w a) (hd a (Finset.mem_insert_self a S))
    have hS := ih (fun i hi ↦ hd i (Finset.mem_insert_of_mem hi))
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Derivation.leibniz,
      smul_eq_mul, smul_eq_mul]
    linear_combination weightedGeometric (w a) (d a) * hS +
      (∏ i ∈ S, weightedGeometric (w i) (d i)) * hga




end
end PaleyWeil

end

section


/-! The exact Newton recurrence for the actual split quadratic-character L-polynomial. -/

open Polynomial Finset
open scoped PowerSeries

namespace PaleyWeil

noncomputable section

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]





theorem coeff_splitEulerProduct (s : Finset K) {n N : ℕ} (hn : n ≤ N) :
    PowerSeries.coeff n (splitEulerProduct s N) = splitLCoeff s n := by
  classical
  rw [splitEulerProduct,
    coeff_finite_weightedEuler _ _ _ _ (fun P ↦ Nat.ne_of_gt (prime_degree_pos P))
      (fun P hP ↦ (mem_primesUpTo N P).mpr (hP.trans hn))]
  exact (splitLCoeff_eq_primeWeights s n).symm



theorem sum_primesOfDegree_eq (s : Finset K) (d k : ℕ) :
    (∑ P ∈ primesOfDegree (K := K) d, splitQuadraticWeight s P ^ k) =
      ∑' P : {P : K[X] // P.Monic ∧ Irreducible P ∧ P.natDegree = d},
        splitQuadraticWeight s P ^ k := by
  classical
  rw [← Finset.tsum_subtype, ← (primeDegreeSubtypeEquiv (K := K) d).tsum_eq]
  rfl

theorem primesOfDegree_pairwiseDisjoint (N : ℕ) :
    Set.PairwiseDisjoint (↑(Finset.range (N + 1))) (primesOfDegree (K := K)) := by
  intro d _ e _ hde
  apply Finset.disjoint_left.mpr
  intro P hPd hPe
  exact hde (((mem_primesOfDegree d P).mp hPd).symm.trans
    ((mem_primesOfDegree e P).mp hPe))

theorem coeff_splitEulerRate (s : Finset K) {n N : ℕ} (hn : n ≤ N) :
    PowerSeries.coeff n (splitEulerRate s N) = splitLPrimeSum s n := by
  classical
  rw [splitEulerRate, map_sum]
  simp_rw [coeff_weightedPrimeRate]
  rw [primesUpTo, Finset.sum_biUnion (primesOfDegree_pairwiseDisjoint N)]
  have hinner (d : ℕ) :
      (∑ P ∈ primesOfDegree (K := K) d,
        if (P : K[X]).natDegree ∣ n ∧ n ≠ 0 then
          ((P : K[X]).natDegree : ℤ) *
            splitQuadraticWeight s P ^ (n / (P : K[X]).natDegree) else 0) =
      if d ∣ n ∧ n ≠ 0 then (d : ℤ) *
        ∑' P : {P : K[X] // P.Monic ∧ Irreducible P ∧ P.natDegree = d},
          splitQuadraticWeight s P ^ (n / d) else 0 := by
    calc
      _ = ∑ P ∈ primesOfDegree (K := K) d,
          if d ∣ n ∧ n ≠ 0 then
            (d : ℤ) * splitQuadraticWeight s P ^ (n / d) else 0 := by
        apply Finset.sum_congr rfl
        intro P hP
        rw [(mem_primesOfDegree d P).mp hP]
      _ = _ := by
        by_cases hdn : d ∣ n ∧ n ≠ 0
        · simp only [if_pos hdn, ← Finset.mul_sum, sum_primesOfDegree_eq]
        · simp only [if_neg hdn, Finset.sum_const_zero]
  simp_rw [hinner]
  rw [← Finset.sum_filter]
  have hdiv : (Finset.range (N + 1)).filter (fun d ↦ d ∣ n ∧ n ≠ 0) = n.divisors := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_range, Nat.mem_divisors]
    constructor
    · exact fun h ↦ h.2
    · intro h
      exact ⟨Nat.lt_succ_of_le ((Nat.le_of_dvd (Nat.pos_of_ne_zero h.2) h.1).trans hn), h⟩
  rw [hdiv]
  rfl

theorem splitEulerProduct_logDerivative (s : Finset K) (N : ℕ) :
    PowerSeries.X * PowerSeries.derivative (R := ℤ) (splitEulerProduct s N) =
      splitEulerRate s N * splitEulerProduct s N := by
  classical
  exact finite_weightedEuler_logDerivative _ _ _
    (fun P _ ↦ Nat.ne_of_gt (prime_degree_pos P))







end
end PaleyWeil

end

/-! The exact Newton recurrence for the actual split quadratic-character L-polynomial. -/
open Polynomial Finset
open scoped PowerSeries
open PaleyWeil
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

theorem solution (s : Finset K) (n : ℕ) :
    (n : ℤ) * splitLCoeff s n =
      ∑ i ∈ Finset.range (n + 1), splitLPrimeSum s i * splitLCoeff s (n - i) := by
  have h := congrArg (PowerSeries.coeff n) (splitEulerProduct_logDerivative s n)
  have hlhs : PowerSeries.coeff n
      (PowerSeries.X * PowerSeries.derivative (R := ℤ) (splitEulerProduct s n)) =
      (n : ℤ) * splitLCoeff s n := by
    cases n with
    | zero => simp
    | succ n =>
      rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative,
        coeff_splitEulerProduct s le_rfl]
      simp [mul_comm]
  rw [hlhs, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro i hi
  have hin : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  rw [coeff_splitEulerRate s hin, coeff_splitEulerProduct s (Nat.sub_le n i)]
