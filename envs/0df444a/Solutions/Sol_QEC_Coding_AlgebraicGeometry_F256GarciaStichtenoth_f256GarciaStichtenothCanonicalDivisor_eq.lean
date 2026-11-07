-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.f256GarciaStichtenothCanonicalDivisor_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:58:48.620741+00:00
-- url     : https://prove2.me/submissions/2892c266-648c-4f61-a609-ec6bf0210ebb

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureGenus
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SelectedFibreSeparation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWZeroRamification
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWRamification
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ExplicitGarciaStichtenothTower
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceClosureCanonicalDivisor_eq


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
open Filter FunctionFieldDifferential
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution (i : ℕ) :
    f256GarciaStichtenothCanonicalDivisor i =
      (16 * (f256GarciaStichtenothAlpha i : ℤ) - 2) • f256GarciaStichtenothDivisorA i +
        ((f256GarciaStichtenothBeta i : ℤ) - 2) • f256GarciaStichtenothDivisorB i -
          f256GarciaStichtenothDivisorD i := sourceClosureCanonicalDivisor_eq (i + 2)
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
