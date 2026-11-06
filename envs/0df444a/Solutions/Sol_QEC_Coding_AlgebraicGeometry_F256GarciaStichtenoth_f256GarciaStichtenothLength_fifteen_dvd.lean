-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.f256GarciaStichtenothLength_fifteen_dvd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:39:58.725958+00:00
-- url     : https://prove2.me/submissions/d3e63e50-a329-47c9-90b7-3ce4037262df

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureGenus
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SelectedFibreSeparation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWZeroRamification
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWRamification
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ExplicitGarciaStichtenothTower
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWRelativeDegree_mul_fifteen


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
open Filter FunctionFieldDifferential
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution (i : ℕ) :
    15 ∣ f256GarciaStichtenothLength i :=
  ⟨sourceGaloisWRelativeDegree (i + 2), (sourceGaloisWRelativeDegree_mul_fifteen (i + 2)).symm⟩
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
