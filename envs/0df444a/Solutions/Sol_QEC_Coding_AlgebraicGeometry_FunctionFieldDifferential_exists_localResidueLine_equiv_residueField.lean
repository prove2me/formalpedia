-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.exists_localResidueLine_equiv_residueField
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:28:42.018063+00:00
-- url     : https://prove2.me/submissions/dc95ac3a-3e1b-44de-b7e2-14de4e85fd88

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_DifferentialLocal
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_GlobalPrincipalDegree
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_TwoChartGlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_CanonicalDifferential

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
open scoped RatFunc
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F]
namespace QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
theorem _root_.solution (P : GlobalPlace k F) :
    Nonempty (Differential.localResidueLine P ≃ₗ[P.valuationRing]
      GlobalPlace.residueField P) := by
  obtain ⟨a, ha⟩ :=
    exists_localDerivativeLatticePrincipalCutoff (k := k) (F := F) P
  exact ⟨localResidueLineEquivResidueField_ofPrincipalCutoff (k := k) (F := F) P a ha⟩
end QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
