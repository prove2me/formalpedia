-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.Differential.globalSimplePoleResidueSum_logarithmicDifferential
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:29:48.699391+00:00
-- url     : https://prove2.me/submissions/a3d941bb-8086-4c65-880c-d62d30c85d97

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_GlobalPrincipalDegree
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_LogarithmicResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Global_LogarithmicResidue
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_globalSimplePoleResidue_logarithmicDifferential_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_logarithmicDifferential_isGlobalSimplePole
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_principalDivisor_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_principalOrder_weighted_sum_eq_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc
open QEC.Coding.AlgebraicGeometry.Differential
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (Polynomial k) F] [Algebra (RatFunc k) F]
variable [IsScalarTower (Polynomial k) (RatFunc k) F]
variable [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F]
namespace QEC.Coding.AlgebraicGeometry.Differential
theorem _root_.solution
    (f : F) (hf : f ≠ 0) :
    globalSimplePoleResidueSum (k := k) (F := F)
        (logarithmicDifferential (k := k) (F := F) f)
        (logarithmicDifferential_isGlobalSimplePole
          (k := k) (F := F) f hf) = 0 := by
  classical
  let u : Fˣ := Units.mk0 f hf
  let D : GlobalPlace k F →₀ ℤ :=
    GlobalPlace.principalDivisor (k := k) (F := F) u
  let Dk : GlobalPlace k F →₀ k :=
    D.mapRange (fun coefficient : ℤ => (coefficient : k)) (by simp)
  rw [globalSimplePoleResidueSum]
  calc
    (globalSimplePoleResidue (k := k) (F := F)
        (logarithmicDifferential (k := k) (F := F) f)
        (logarithmicDifferential_isGlobalSimplePole
          (k := k) (F := F) f hf)).sum (fun _ residue => residue) =
        Dk.sum (fun P coefficient => coefficient *
          (GlobalPlace.residueDegree (k := k) (F := F) P : k)) := by
      apply Finsupp.sum_congr_of_eq_on_union
      · intro P _
        rw [globalSimplePoleResidue_logarithmicDifferential_apply
          (k := k) (F := F) f hf P]
        simp only [Dk, Finsupp.mapRange_apply, D,
          GlobalPlace.principalDivisor_apply, u, Units.val_mk0]
        ring
      · intro P _
        rfl
      · intro P _
        simp
    _ = D.sum (fun P coefficient => (coefficient : k) *
        (GlobalPlace.residueDegree (k := k) (F := F) P : k)) := by
      simpa only [Dk] using
        (Finsupp.sum_mapRange_index (g := D)
          (h := fun P coefficient => coefficient *
            (GlobalPlace.residueDegree (k := k) (F := F) P : k))
          (fun _ => by simp))
    _ = 0 := by
      have hdegree := congrArg (fun z : ℤ => (z : k))
        (GlobalPlace.principalOrder_weighted_sum_eq_zero k F u)
      simpa only [D, Int.cast_finsupp_sum, Int.cast_mul, Int.cast_natCast,
        Int.cast_zero] using hdegree
end QEC.Coding.AlgebraicGeometry.Differential
