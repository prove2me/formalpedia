-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:17:43.068375+00:00
-- url     : https://prove2.me/submissions/c4207172-e148-4cfb-94f9-a1235a641a00

import Mathlib.Algebra.GroupWithZero.WithZero
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic
import Mathlib.Algebra.Order.Hom.MonoidWithZero
import Mathlib.Algebra.Order.Hom.TypeTags
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Data.Finsupp.Basic
import Mathlib.FieldTheory.Finite.Valuation
import Mathlib.GroupTheory.ArchimedeanDensely
import Mathlib.NumberTheory.FunctionField
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Valuation.Discrete.RankOne
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.Valuation.ValuationSubring
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AffinePlaceDegree
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_AffinePrincipalDivisor
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_GlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_InverseInfinityFibre
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RationalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_TwoChartGlobalPlace

set_option autoImplicit false
open scoped Polynomial RatFunc WithZero
open MonoidWithZeroHom
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
namespace QEC.Coding.AlgebraicGeometry
namespace GlobalPlace
theorem _root_.solution
    {k F : Type*} [Field k] [Finite k] [Field F]
    (oldAlgebra newAlgebra : Algebra k F)
    (P : @GlobalPlace k F _ _ _ oldAlgebra) :
    @GlobalPlace.valuation k F _ _ _ newAlgebra
        (GlobalPlace.repackageEquiv oldAlgebra newAlgebra P) =
      @GlobalPlace.valuation k F _ _ _ oldAlgebra P :=
  rfl
end GlobalPlace
end QEC.Coding.AlgebraicGeometry
