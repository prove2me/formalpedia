-- Prove2me | solution 1 for PaleyWeil.splitLPolynomial_logDerivative_of_recurrence
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-11-24T17:43:34.546104+00:00
-- url     : https://prove2.me/submissions/9eced2a3-96e2-429b-9474-41a820ba4476

import Definitions.Def_Sensitivity214439_Phase0_RiemannHypothesisCurves_SplitLPolynomial
import Definitions.Def_Sensitivity214439_Phase0_RiemannHypothesisCurves_SplitLSeriesDefs
import Definitions.Def_Sensitivity214439_Phase0_RiemannHypothesisCurves_SplitQuadraticWeight
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Data.Complex.Basic
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Theorems.Thm_PaleyWeil_split_monic_sum_eq_zero

namespace Finset
end Finset
namespace PaleyWeil
end PaleyWeil
namespace Polynomial
end Polynomial

section


open Polynomial Finset

namespace PaleyWeil



@[simp]
theorem splitQuadraticWeight_one {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (s : Finset K) : splitQuadraticWeight s (1 : K[X]) = 1 := by
  simp [splitQuadraticWeight]








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



theorem splitLCoeff_eq_zero_of_card_le {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (hK : ringChar K ≠ 2) (s : Finset K) (hs : s.Nonempty) (n : ℕ) (hn : s.card ≤ n) :
    splitLCoeff s n = 0 := split_monic_sum_eq_zero hK s hs n hn




end PaleyWeil

end

section


open Polynomial Finset
open scoped PowerSeries

namespace PaleyWeil

noncomputable section

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]



theorem coeff_splitLPolynomial (hK : ringChar K ≠ 2) (s : Finset K)
    (hs : s.Nonempty) (n : ℕ) :
    (splitLPolynomial s).coeff n = (splitLCoeff s n : ℂ) := by
  classical
  by_cases hn : n < s.card
  · exact Polynomial.ofFn_coeff_eq_val_of_lt _ hn
  · rw [splitLPolynomial, Polynomial.ofFn_coeff_eq_zero_of_ge _ (Nat.le_of_not_gt hn),
      splitLCoeff_eq_zero_of_card_le hK s hs n (Nat.le_of_not_gt hn), Int.cast_zero]










end
end PaleyWeil

end

open Polynomial Finset
open scoped PowerSeries
open PaleyWeil
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

theorem solution
    (hK : ringChar K ≠ 2) (s : Finset K) (hs : s.Nonempty)
    (hrec : ∀ n : ℕ, (n : ℤ) * splitLCoeff s n =
      ∑ i ∈ Finset.range (n + 1), splitLPrimeSum s i * splitLCoeff s (n - i)) :
    PowerSeries.X * PowerSeries.derivative (R := ℂ) (splitLPolynomial s : ℂ⟦X⟧) =
      PowerSeries.mk (fun n ↦ (splitLPrimeSum s n : ℂ)) *
        (splitLPolynomial s : ℂ⟦X⟧) := by
  ext n
  have hlhs : PowerSeries.coeff n
      (PowerSeries.X * PowerSeries.derivative (R := ℂ) (splitLPolynomial s : ℂ⟦X⟧)) =
      (n : ℂ) * (splitLCoeff s n : ℂ) := by
    cases n with
    | zero => simp
    | succ n =>
      rw [← pow_one (PowerSeries.X : ℂ⟦X⟧), PowerSeries.coeff_X_pow_mul,
        PowerSeries.coeff_derivative, Polynomial.coeff_coe,
        coeff_splitLPolynomial hK s hs]
      simp [mul_comm]
  rw [hlhs, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [PowerSeries.coeff_mk, Polynomial.coeff_coe, coeff_splitLPolynomial hK s hs]
  exact_mod_cast hrec n
