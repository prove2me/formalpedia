-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceClosureCanonicalDifferential_selected_residue
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:46:25.318326+00:00
-- url     : https://prove2.me/submissions/9e944dbe-6846-4c4a-9324-fbd43638dff0

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureDifferentialDivisor
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisSelectedDivisor
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureCanonicalDifferential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_simplePoleResidue_logarithmicDifferential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisClosureSelectedRationalPlace_order_vanishingFunction


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
theorem _root_.solution (m : ℕ)
    (j : Fin (sourceGaloisClosureSelectedLength m)) :
    Differential.simplePoleResidue (sourceGaloisClosureSelectedRationalPlace m j).place
      (sourceClosureCanonicalDifferentialAtPlace m (sourceGaloisClosureSelectedRationalPlace m j).place) =
        1 := by
  rw [sourceClosureCanonicalDifferentialAtPlace,
    Differential.simplePoleResidue_logarithmicDifferential,
    sourceGaloisClosureSelectedRationalPlace_order_vanishingFunction, Int.cast_one]
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
