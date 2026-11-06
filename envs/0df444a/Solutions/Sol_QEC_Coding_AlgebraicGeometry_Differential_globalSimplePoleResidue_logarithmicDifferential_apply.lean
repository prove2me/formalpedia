-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.Differential.globalSimplePoleResidue_logarithmicDifferential_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:47:04.350399+00:00
-- url     : https://prove2.me/submissions/9c1faba5-7054-4c4f-83dc-e474f14809ec

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_GlobalPrincipalDegree
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_LogarithmicResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Global_LogarithmicResidue
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_simplePoleTraceResidue_logarithmicDifferential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_globalSimplePoleResidue_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_logarithmicDifferential_isGlobalSimplePole


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
    (f : F) (hf : f ≠ 0) (P : GlobalPlace k F) :
    globalSimplePoleResidue (k := k) (F := F)
        (logarithmicDifferential (k := k) (F := F) f)
        (logarithmicDifferential_isGlobalSimplePole
          (k := k) (F := F) f hf) P =
      (GlobalPlace.residueDegree (k := k) (F := F) P : k) * (P.order f : k) := by
  rw [globalSimplePoleResidue_apply]
  exact simplePoleTraceResidue_logarithmicDifferential
    (k := k) (F := F) P f hf
end QEC.Coding.AlgebraicGeometry.Differential
