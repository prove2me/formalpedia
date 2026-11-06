-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.DirectRelNormCoefficient.normalizedFactors_relNorm_eq_bind
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:17:19.550065+00:00
-- url     : https://prove2.me/submissions/1b6ef258-d7c6-440a-b4f9-fe231f2e3d4b

import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.RamificationInertia.Inertia
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AffinePlaceDegree
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_DirectNormCount
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_SeparableNormalCover
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_DirectRelNormCoefficient
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_SeparableNormalCover_direct_relNorm_eq_pow
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
private theorem factor_isMaximal_and_under_isMaximal (I P : Ideal B)
    (hP : P ∈ normalizedFactors I) : P.IsMaximal ∧ (P.under R).IsMaximal := by
  have hprime : Prime P := prime_of_normalized_factor P hP
  have hP0 : P ≠ (⊥ : Ideal B) := by
    simpa only [Ideal.zero_eq_bot] using hprime.ne_zero
  have hPprime : P.IsPrime := Ideal.isPrime_of_prime hprime
  have hPmax : P.IsMaximal := hPprime.isMaximal hP0
  letI : P.IsMaximal := hPmax
  exact ⟨hPmax, Ideal.IsMaximal.under R P⟩
private theorem direct_relNorm_factor_eq_pow (I P : Ideal B)
    (hP : P ∈ normalizedFactors I) :
    Ideal.relNorm R P = (P.under R) ^ (P.under R).inertiaDeg' P := by
  obtain ⟨hPmax, hqmax⟩ := factor_isMaximal_and_under_isMaximal k F I P hP
  letI : P.IsMaximal := hPmax
  letI : (P.under R).IsMaximal := hqmax
  letI : P.LiesOver (P.under R) := ⟨rfl⟩
  exact
    SeparableNormalCover.direct_relNorm_eq_pow k F P (P.under R)
private theorem under_factor_ne_bot (I P : Ideal B)
    (hP : P ∈ normalizedFactors I) : P.under R ≠ ⊥ := by
  obtain ⟨_, hqmax⟩ := factor_isMaximal_and_under_isMaximal k F I P hP
  exact Ring.ne_bot_of_isMaximal_of_not_isField hqmax (Ideal.polynomial_not_isField k)
private theorem normalizedFactors_relNorm_factor (I P : Ideal B)
    (hP : P ∈ normalizedFactors I) :
    normalizedFactors (Ideal.relNorm R P) =
      Multiset.replicate ((P.under R).inertiaDeg' P) (P.under R) := by
  rw [direct_relNorm_factor_eq_pow k F I P hP]
  have hq0 : P.under R ≠ ⊥ := under_factor_ne_bot k F I P hP
  obtain ⟨_, hqmax⟩ := factor_isMaximal_and_under_isMaximal k F I P hP
  have hqprime : Prime (P.under R) :=
    Ideal.prime_of_isPrime hq0 hqmax.isPrime
  rw [hqprime.irreducible.normalizedFactors_pow, normalize_eq]
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
theorem _root_.solution (I : Ideal B) (hI : I ≠ ⊥) :
    normalizedFactors (Ideal.relNorm R I) =
      (normalizedFactors I).bind fun P =>
        Multiset.replicate ((P.under R).inertiaDeg' P) (P.under R) := by
  have hfactor : (normalizedFactors I).prod = I :=
    Ideal.prod_normalizedFactors_eq_self hI
  conv_lhs => rw [← hfactor]
  rw [map_multiset_prod]
  rw [normalizedFactors_multiset_prod]
  · apply congrArg Multiset.sum
    rw [Multiset.map_map]
    apply Multiset.map_congr rfl
    intro P hP
    exact normalizedFactors_relNorm_factor k F I P hP
  · intro hzero
    obtain ⟨P, hP, hnormP⟩ := Multiset.mem_map.mp hzero
    have hnormPbot : Ideal.relNorm R P = ⊥ := by
      simpa only [Ideal.zero_eq_bot] using hnormP
    have hP0 : P ≠ (⊥ : Ideal B) := by
      simpa only [Ideal.zero_eq_bot] using (prime_of_normalized_factor P hP).ne_zero
    exact hP0 (Ideal.relNorm_eq_bot_iff.mp hnormPbot)
end QEC.Coding.AlgebraicGeometry.DirectRelNormCoefficient
