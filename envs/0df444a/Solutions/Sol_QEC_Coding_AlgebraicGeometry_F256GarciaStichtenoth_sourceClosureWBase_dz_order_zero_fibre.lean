-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceClosureWBase_dz_order_zero_fibre
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:12:48.18634+00:00
-- url     : https://prove2.me/submissions/ed703306-8262-4201-92c8-9886f4c6ff48

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureDifferentialOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_RationalDifferentialTransport
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWClosurePlaces
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_WBaseDifferentialOrder
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceClosureWBase_generator_ne_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceClosureWBase_generator_derivative_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_differentialGenerator_order_of_order_one_or_neg_one
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_functionFieldDifferentialGenerator_ne_zero


set_option autoImplicit false
open IntermediateField QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 5000] Algebra.toSMul Algebra.toModule
attribute [local instance] wConstantBaseTower
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.wBaseField
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.wBaseOriginalBaseAlgebra
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.wBaseOriginalRationalAlgebra
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.wBaseOriginalConstantAlgebra
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.wBaseCharacteristic
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.wBaseConstantTower
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution (m : ℕ)
    (P : GlobalPlace F256 (sourceClosureWBase m))
    (hw : P.order (sourceGaloisWClosureGenerator m) = 1) :
    differentialOrder P (functionFieldDifferentialGenerator (k := F256) (F := sourceClosureWBase m))
      functionFieldDifferentialGenerator_ne_zero = 14 := by
  obtain ⟨_, h⟩ := differentialGenerator_order_of_order_one_or_neg_one P
    (sourceGaloisWClosureGenerator m) (sourceClosureWBase_generator_ne_zero m) (.inl hw)
  rw [h, sourceClosureWBase_generator_derivative_order, hw]
  norm_num
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
