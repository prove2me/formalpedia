-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.Differential.simplePoleTraceResidue_logarithmicDifferential
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:45:42.069194+00:00
-- url     : https://prove2.me/submissions/0602d8b9-4740-41b2-80f0-5b905e75b418

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_GlobalPrincipalDegree
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_LogarithmicResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Global_LogarithmicResidue
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_logarithmicDifferential_isGlobalSimplePole
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_simplePoleResidue_logarithmicDifferential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_residueDegree_eq_finrank
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
    (P : GlobalPlace k F) (f : F) (hf : f ≠ 0) :
    simplePoleTraceResidue (k := k) (F := F) P
        (logarithmicDifferential (k := k) (F := F) f)
        (logarithmicDifferential_isGlobalSimplePole
          (k := k) (F := F) f hf P) =
      (GlobalPlace.residueDegree (k := k) (F := F) P : k) * (P.order f : k) := by
  letI : Algebra k P.residueField := GlobalPlace.residueAlgebra P
  letI : FiniteDimensional k P.residueField :=
    GlobalPlace.residueField_finiteDimensional P
  change Algebra.trace k P.residueField
      (simplePoleResidue (k := k) (F := F) P
        ⟨logarithmicDifferential (k := k) (F := F) f,
          logarithmicDifferential_isGlobalSimplePole
            (k := k) (F := F) f hf P⟩) = _
  have hresidue :
      simplePoleResidue (k := k) (F := F) P
          ⟨logarithmicDifferential (k := k) (F := F) f,
            logarithmicDifferential_isGlobalSimplePole
              (k := k) (F := F) f hf P⟩ =
        (P.order f : P.residueField) := by
    rw [show (⟨logarithmicDifferential (k := k) (F := F) f,
        logarithmicDifferential_isGlobalSimplePole
          (k := k) (F := F) f hf P⟩ : simplePoleDifferentialLattice P) =
        logarithmicDifferentialAtSimplePole (k := k) (F := F) P f hf by
      apply Subtype.ext
      rfl]
    exact simplePoleResidue_logarithmicDifferential (k := k) (F := F) P f hf
  rw [hresidue, ← map_intCast (algebraMap k P.residueField),
    Algebra.trace_algebraMap, GlobalPlace.residueDegree_eq_finrank]
  simp only [nsmul_eq_mul]
end QEC.Coding.AlgebraicGeometry.Differential
