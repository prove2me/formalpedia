-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.DirectRelNormCoefficient.direct_relNorm_coefficient_eq_sum_primesOver
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:21:27.876765+00:00
-- url     : https://prove2.me/submissions/719f4ec3-279c-4c32-a96a-99ba0402a0cc

import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.RamificationInertia.Inertia
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AffinePlaceDegree
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_DirectNormCount
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_SeparableNormalCover
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_DirectRelNormCoefficient
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectRelNormCoefficient_count_bind_replicate_eq_sum
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectRelNormCoefficient_normalizedFactors_relNorm_eq_bind
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero


section
namespace QEC.Coding.AlgebraicGeometry.DirectRelNormCoefficient
open scoped BigOperators Polynomial RatFunc nonZeroDivisors
open UniqueFactorizationMonoid
section finite_collection
variable {alpha beta : Type*} [DecidableEq alpha] [DecidableEq beta]
end finite_collection
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]
local notation3 "R" => k[X]
local notation3 "B" => directRingOfIntegers k F
attribute [local instance] directRelNormCoefficient_isTorsionFree
private theorem direct_relNorm_coefficient_over_factors (I : Ideal B) (hI : I ≠ ⊥)
    (p : Ideal R) :
    Multiset.count p (normalizedFactors (Ideal.relNorm R I)) =
      ∑ P ∈ (normalizedFactors I).toFinset,
        (if P.under R = p then (P.under R).inertiaDeg' P else 0) *
          Multiset.count P (normalizedFactors I) := by
  rw [normalizedFactors_relNorm_eq_bind k F I hI]
  exact count_bind_replicate_eq_sum (normalizedFactors I) (fun P => P.under R)
    (fun P => (P.under R).inertiaDeg' P) p
private theorem direct_collect_factors_to_primesOverFinset (I : Ideal B)
    (p : Ideal R) [p.IsMaximal] (hp0 : p ≠ ⊥) :
    ∑ P ∈ (normalizedFactors I).toFinset,
      (if P.under R = p then (P.under R).inertiaDeg' P else 0) *
        Multiset.count P (normalizedFactors I) =
      ∑ P ∈ IsDedekindDomain.primesOverFinset p B,
        p.inertiaDeg' P * Multiset.count P (normalizedFactors I) := by
  classical
  let s := (normalizedFactors I).toFinset.filter fun P => P.under R = p
  simp_rw [ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  change (∑ P ∈ s, (P.under R).inertiaDeg' P *
      Multiset.count P (normalizedFactors I)) = _
  have hs : s ⊆ IsDedekindDomain.primesOverFinset p B := by
    intro P hP
    rw [Finset.mem_filter] at hP
    obtain ⟨hPfactor, hPunder⟩ := hP
    have hprime : Prime P :=
      prime_of_normalized_factor P (by simpa only [Multiset.mem_toFinset] using hPfactor)
    have hPprime : P.IsPrime := Ideal.isPrime_of_prime hprime
    have hPover : P.LiesOver p := ⟨hPunder.symm⟩
    exact (IsDedekindDomain.mem_primesOverFinset_iff hp0 B).mpr ⟨hPprime, hPover⟩
  calc
    ∑ P ∈ s, (P.under R).inertiaDeg' P *
        Multiset.count P (normalizedFactors I) =
      ∑ P ∈ IsDedekindDomain.primesOverFinset p B,
        (P.under R).inertiaDeg' P * Multiset.count P (normalizedFactors I) := by
      apply Finset.sum_subset hs
      intro P hPover hPnot
      have hPnotFactor : P ∉ normalizedFactors I := by
        intro hPfactor
        apply hPnot
        dsimp only [s]
        rw [Finset.mem_filter]
        refine ⟨Multiset.mem_toFinset.mpr hPfactor, ?_⟩
        obtain ⟨_, hPlies⟩ :=
          (IsDedekindDomain.mem_primesOverFinset_iff hp0 B).mp hPover
        letI : P.LiesOver p := hPlies
        exact (Ideal.over_def P p).symm
      simp only [Multiset.count_eq_zero_of_notMem hPnotFactor, mul_zero]
    _ = ∑ P ∈ IsDedekindDomain.primesOverFinset p B,
        p.inertiaDeg' P * Multiset.count P (normalizedFactors I) := by
      apply Finset.sum_congr rfl
      intro P hPfiber
      obtain ⟨_, hPover⟩ :=
        (IsDedekindDomain.mem_primesOverFinset_iff hp0 B).mp hPfiber
      letI : P.LiesOver p := hPover
      rw [← Ideal.over_def P p]
end QEC.Coding.AlgebraicGeometry.DirectRelNormCoefficient
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.DirectRelNormCoefficient
open scoped BigOperators Polynomial RatFunc nonZeroDivisors
open UniqueFactorizationMonoid
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]
local notation3 "R" => k[X]
local notation3 "B" => directRingOfIntegers k F
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectRelNormCoefficient.directRelNormCoefficient_isTorsionFree
attribute [local instance] directRelNormCoefficient_isTorsionFree
namespace QEC.Coding.AlgebraicGeometry.DirectRelNormCoefficient
theorem _root_.solution (I : Ideal B) (hI : I ≠ ⊥)
    (p : Ideal R) [p.IsMaximal] (hp0 : p ≠ ⊥) :
    Multiset.count p (normalizedFactors (Ideal.relNorm R I)) =
      ∑ P ∈ IsDedekindDomain.primesOverFinset p B,
        p.inertiaDeg' P * Multiset.count P (normalizedFactors I) := by
  rw [direct_relNorm_coefficient_over_factors k F I hI p]
  exact direct_collect_factors_to_primesOverFinset k F I p hp0
end QEC.Coding.AlgebraicGeometry.DirectRelNormCoefficient
