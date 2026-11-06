-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.integralClosure_moduleFree_over_integralLocalBase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:34:27.876039+00:00
-- url     : https://prove2.me/submissions/acda0631-42bb-4583-a0cb-32d6c06cc4cc

import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DedekindDomain.PID
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_LocalIntegralClosureFree
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_isPrincipalIdealRing_of_isLocalRing_of_isIntegral

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution
    (A B K L C : Type*)
    [CommRing A] [CommRing B] [Field K] [Field L] [CommRing C]
    [IsDomain A] [IsLocalRing A] [IsDedekindDomain B]
    [Algebra A B] [Algebra.IsIntegral A B]
    [Module.IsTorsionFree A B]
    [Algebra B K] [IsFractionRing B K]
    [Algebra K L] [Algebra B L] [IsScalarTower B K L]
    [Algebra C L] [IsIntegralClosure C B L]
    [Algebra B C] [IsScalarTower B C L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Module.IsTorsionFree B L] :
    Module.Free B C := by
  letI : IsPrincipalIdealRing B :=
    isPrincipalIdealRing_of_isLocalRing_of_isIntegral A B
  exact IsIntegralClosure.module_free B K L C
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
