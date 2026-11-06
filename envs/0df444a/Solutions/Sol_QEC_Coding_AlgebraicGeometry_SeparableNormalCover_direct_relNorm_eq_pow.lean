-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.SeparableNormalCover.direct_relNorm_eq_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:13:33.335295+00:00
-- url     : https://prove2.me/submissions/5d7faed3-4cc1-4387-8f44-d3043470b003

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AffinePlaceDegree
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.RingTheory.RamificationInertia.Inertia
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_SeparableNormalCover
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero


section
namespace QEC.Coding.AlgebraicGeometry.SeparableNormalCover
open scoped Polynomial RatFunc
noncomputable section
attribute [local instance] FractionRing.liftAlgebra in
private theorem relNorm_eq_pow_of_galois_integral_cover
    {R S : Type*} (T : Type*) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [IsDedekindDomain R] [CommRing S] [IsDomain S] [IsIntegrallyClosed S]
    [IsDedekindDomain S] [CommRing T] [IsDomain T] [IsIntegrallyClosed T]
    [IsDedekindDomain T] [Algebra R S] [Algebra S T] [Algebra R T]
    [IsScalarTower R S T] [Module.Finite R S] [Module.IsTorsionFree R S]
    [Module.Finite S T] [Module.IsTorsionFree S T] [Module.Finite R T]
    [Module.IsTorsionFree R T] [Algebra.IsIntegral S T]
    [IsGalois (FractionRing R) (FractionRing T)]
    [IsGalois (FractionRing S) (FractionRing T)]
    (P : Ideal S) (p : Ideal R) [P.LiesOver p] [P.IsMaximal] [p.IsMaximal] :
    Ideal.relNorm R P = p ^ p.inertiaDeg' P := by
  obtain ⟨Q, hQmax, hQover⟩ : ∃ Q : Ideal T, Q.IsMaximal ∧ Q.LiesOver P :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := T) P
  letI : Q.IsMaximal := hQmax
  letI : Q.LiesOver P := hQover
  letI : Q.LiesOver p := Ideal.LiesOver.trans Q P p
  have hQp : Ideal.relNorm R Q = p ^ p.inertiaDeg' Q := by
    simpa only [Ideal.inertiaDeg'_eq_inertiaDeg] using
      Ideal.relNorm_eq_pow_of_isPrime_isGalois Q p
  have hQP : Ideal.relNorm S Q = P ^ P.inertiaDeg' Q := by
    simpa only [Ideal.inertiaDeg'_eq_inertiaDeg] using
      Ideal.relNorm_eq_pow_of_isPrime_isGalois Q P
  rw [← Ideal.relNorm_relNorm R S, hQP, map_pow] at hQp
  rwa [Ideal.inertiaDeg_algebra_tower p P Q, pow_mul, pow_left_inj] at hQp
  exact Nat.ne_zero_iff_zero_lt.mpr (Ideal.inertiaDeg'_pos P Q)
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]
local notation3 "R" => k[X]
local notation3 "B" => directRingOfIntegers k F
local notation3 "K" => FractionRing R
local notation3 "L" => FractionRing B
local notation3 "M" => SeparableClosure K
local notation3 "E" => IntermediateField.normalClosure K L M
local notation "T" => integralClosure B E
end
end QEC.Coding.AlgebraicGeometry.SeparableNormalCover
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.SeparableNormalCover
open scoped Polynomial RatFunc
noncomputable section
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]
local notation3 "R" => k[X]
local notation3 "B" => directRingOfIntegers k F
local notation3 "K" => FractionRing R
local notation3 "L" => FractionRing B
attribute [local instance] QEC.Coding.AlgebraicGeometry.SeparableNormalCover._p2m_local_instance_ece2c1af97_56
attribute [local instance] QEC.Coding.AlgebraicGeometry.SeparableNormalCover._p2m_local_instance_ece2c1af97_60
attribute [local instance] QEC.Coding.AlgebraicGeometry.SeparableNormalCover._p2m_local_instance_ece2c1af97_62
attribute [local instance] QEC.Coding.AlgebraicGeometry.SeparableNormalCover._p2m_local_instance_ece2c1af97_76
local notation3 "M" => SeparableClosure K
attribute [local instance] QEC.Coding.AlgebraicGeometry.SeparableNormalCover._p2m_local_instance_ece2c1af97_87
attribute [local instance] QEC.Coding.AlgebraicGeometry.SeparableNormalCover._p2m_local_instance_ece2c1af97_89
local notation3 "E" => IntermediateField.normalClosure K L M
attribute [local instance] QEC.Coding.AlgebraicGeometry.SeparableNormalCover._p2m_local_instance_ece2c1af97_96
attribute [local instance] QEC.Coding.AlgebraicGeometry.SeparableNormalCover._p2m_local_instance_ece2c1af97_98
attribute [local instance] QEC.Coding.AlgebraicGeometry.SeparableNormalCover._p2m_local_instance_ece2c1af97_100
attribute [local instance] QEC.Coding.AlgebraicGeometry.SeparableNormalCover._p2m_local_instance_ece2c1af97_102
local notation "T" => integralClosure B E
attribute [local instance] QEC.Coding.AlgebraicGeometry.SeparableNormalCover._p2m_local_instance_ece2c1af97_108
attribute [local instance] QEC.Coding.AlgebraicGeometry.SeparableNormalCover._p2m_local_instance_ece2c1af97_110
attribute [local instance] QEC.Coding.AlgebraicGeometry.SeparableNormalCover._p2m_local_instance_ece2c1af97_112
attribute [local instance] QEC.Coding.AlgebraicGeometry.SeparableNormalCover._p2m_local_instance_ece2c1af97_114
attribute [local instance] QEC.Coding.AlgebraicGeometry.SeparableNormalCover._p2m_local_instance_ece2c1af97_116
attribute [local instance] QEC.Coding.AlgebraicGeometry.SeparableNormalCover._p2m_local_instance_ece2c1af97_118
attribute [local instance] QEC.Coding.AlgebraicGeometry.SeparableNormalCover._p2m_local_instance_ece2c1af97_120
attribute [local instance] QEC.Coding.AlgebraicGeometry.SeparableNormalCover._p2m_local_instance_ece2c1af97_125
attribute [local instance] QEC.Coding.AlgebraicGeometry.SeparableNormalCover._p2m_local_instance_ece2c1af97_131
attribute [local instance] QEC.Coding.AlgebraicGeometry.SeparableNormalCover._p2m_local_instance_ece2c1af97_135
attribute [local instance] QEC.Coding.AlgebraicGeometry.SeparableNormalCover._p2m_local_instance_ece2c1af97_138
attribute [local instance] QEC.Coding.AlgebraicGeometry.SeparableNormalCover._p2m_local_instance_ece2c1af97_141
attribute [local instance] QEC.Coding.AlgebraicGeometry.SeparableNormalCover._p2m_local_instance_ece2c1af97_146
attribute [local instance] QEC.Coding.AlgebraicGeometry.SeparableNormalCover._p2m_local_instance_ece2c1af97_148
attribute [local instance] QEC.Coding.AlgebraicGeometry.SeparableNormalCover._p2m_local_instance_ece2c1af97_151
attribute [local instance] QEC.Coding.AlgebraicGeometry.SeparableNormalCover._p2m_local_instance_ece2c1af97_154
attribute [local instance] QEC.Coding.AlgebraicGeometry.SeparableNormalCover._p2m_local_instance_ece2c1af97_157
attribute [local instance] QEC.Coding.AlgebraicGeometry.SeparableNormalCover._p2m_local_instance_ece2c1af97_160
attribute [local instance] QEC.Coding.AlgebraicGeometry.SeparableNormalCover._p2m_local_instance_ece2c1af97_162
attribute [local instance] QEC.Coding.AlgebraicGeometry.SeparableNormalCover._p2m_local_instance_ece2c1af97_164
attribute [local instance] QEC.Coding.AlgebraicGeometry.SeparableNormalCover._p2m_local_instance_ece2c1af97_168
attribute [local instance] QEC.Coding.AlgebraicGeometry.SeparableNormalCover._p2m_local_instance_ece2c1af97_170
attribute [local instance] QEC.Coding.AlgebraicGeometry.SeparableNormalCover._p2m_local_instance_ece2c1af97_185
attribute [local instance] QEC.Coding.AlgebraicGeometry.SeparableNormalCover.directBFracAlgebra
attribute [local instance] QEC.Coding.AlgebraicGeometry.SeparableNormalCover._p2m_local_instance_ece2c1af97_189
attribute [local instance] QEC.Coding.AlgebraicGeometry.SeparableNormalCover._p2m_local_instance_ece2c1af97_190
attribute [local instance] QEC.Coding.AlgebraicGeometry.SeparableNormalCover._p2m_local_instance_ece2c1af97_194
namespace QEC.Coding.AlgebraicGeometry.SeparableNormalCover
theorem _root_.solution
    (P : Ideal B) (p : Ideal R) [P.LiesOver p] [P.IsMaximal] [p.IsMaximal] :
    Ideal.relNorm R P = p ^ p.inertiaDeg' P := by
  letI : IsGalois L (FractionRing T) :=
    IsGalois.tower_top_of_isGalois K L (FractionRing T)
  exact relNorm_eq_pow_of_galois_integral_cover T P p
end QEC.Coding.AlgebraicGeometry.SeparableNormalCover
