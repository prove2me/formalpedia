-- Prove2me | solution 2 for QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalInfinity_residueDegree_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T19:37:41.420772+00:00
-- url     : https://prove2.me/submissions/935b6739-3cbe-45e9-993b-4bffb54c8e2c

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_RationalBaseInfinityCancellation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RationalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_TwoChartGlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_InfinityResidue
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalInfinity_constantsToResidue_surjective
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_residueDegree_eq_finrank
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation



set_option autoImplicit false
open scoped Polynomial RatFunc WithZero
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.GlobalPlace
variable {k : Type*} [Field k] [Finite k]
namespace QEC.Coding.AlgebraicGeometry.GlobalPlace
theorem _root_.solution :
    residueDegree (k := k) (F := RatFunc k) (rationalInfinity k) = 1 := by
  let P := rationalInfinity k
  letI : Algebra k P.residueField := residueAlgebra P
  letI : FiniteDimensional k P.residueField :=
    residueField_finiteDimensional P
  rw [residueDegree_eq_finrank]
  apply Module.finrank_of_bijective_algebraMap
  constructor
  · exact (algebraMap k P.residueField).injective
  · simpa only [P, residueAlgebra, RingHom.algebraMap_toAlgebra] using
      (rationalInfinity_constantsToResidue_surjective (k := k))
end QEC.Coding.AlgebraicGeometry.GlobalPlace
