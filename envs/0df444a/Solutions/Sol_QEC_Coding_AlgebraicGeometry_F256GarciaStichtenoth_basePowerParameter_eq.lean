-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.basePowerParameter_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:18:40.738637+00:00
-- url     : https://prove2.me/submissions/2dd2ee4d-a634-4ca4-a278-88066a5bc362

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Divisors
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_PolarDegree
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_BaseParameter

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [-instance]
  selectedFieldField
  selectedFieldConstantAlgebra
  selectedFieldRatFuncAlgebra
  selectedFieldConstantTower
  selectedFieldFunctionField
  selectedFieldRatFuncSeparable
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.basePowerParameterConstantAlgebra
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.basePowerParameterRatFuncAlgebra
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.basePowerParameterFunctionField
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.basePowerParameterSeparable
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution (m : ℕ) :
    basePowerParameter m =
      GlobalPlace.chartVariable (k := F256) (F := Field m) ^ 17 :=
  rfl
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
