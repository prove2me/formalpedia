-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceClosureCanonicalDivisor_isCanonical
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:32:48.671835+00:00
-- url     : https://prove2.me/submissions/a99000d7-529f-42ff-aa2c-d0c00d12674c

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureDifferentialDivisor
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisSelectedDivisor
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureCanonicalDifferential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_differentialDivisor_isCanonical


set_option autoImplicit false
open QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.canonicalDifferentialModule
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.canonicalDifferentialSMul
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution (m : ℕ) :
    IsCanonicalDivisor (k := F256) (F := SourceGaloisClosureField m)
      (sourceClosureCanonicalDivisor m) :=
  differentialDivisor_isCanonical _ _
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
