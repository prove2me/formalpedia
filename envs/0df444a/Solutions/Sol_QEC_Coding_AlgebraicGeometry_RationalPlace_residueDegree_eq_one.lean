-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.RationalPlace.residueDegree_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:27:31.813197+00:00
-- url     : https://prove2.me/submissions/64fb62fe-3a30-4a2b-940f-411d5c56c000

import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_GlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RationalPlace
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RationalPlace_constantsToResidue_bijective
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.RationalPlace
variable {k F : Type*}
variable [Field k] [Finite k] [Field F] [Algebra k F]
namespace QEC.Coding.AlgebraicGeometry.RationalPlace
theorem _root_.solution (Q : RationalPlace k F) :
    GlobalPlace.residueDegreeOfFinite Q.place Q.hasFiniteResidueDegree = 1 := by
  unfold GlobalPlace.residueDegreeOfFinite
  letI : Algebra k (GlobalPlace.residueField Q.place) :=
    GlobalPlace.residueAlgebra Q.place
  letI : FiniteDimensional k (GlobalPlace.residueField Q.place) :=
    Q.hasFiniteResidueDegree
  apply Module.finrank_of_bijective_algebraMap
  simpa only [GlobalPlace.residueAlgebra, RingHom.algebraMap_toAlgebra] using
    Q.constantsToResidue_bijective
end QEC.Coding.AlgebraicGeometry.RationalPlace
