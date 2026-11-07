-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceClosureCanonicalDivisor_degree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:57:40.449206+00:00
-- url     : https://prove2.me/submissions/21ff83d2-3ea2-44ee-ae4b-c3eedc4b9617

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureCanonicalDifferential
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureFullConstants
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_Theorem
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureGenus
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_canonicalDivisor_degree_of_constantAlgebra_eq
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceClosureCanonicalDivisor_isCanonical


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution (m : ℕ) :
    Divisor.degree GlobalPlace.residueDegree (sourceClosureCanonicalDivisor m) =
      2 * (sourceClosureGenus m : ℤ) - 2 := by
  exact canonicalDivisor_degree_of_constantAlgebra_eq F256 (SourceGaloisClosureField m)
    (sourceClosureDirectConstant_eq m).symm
    (sourceClosureCanonicalDivisor_isCanonical m)
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
