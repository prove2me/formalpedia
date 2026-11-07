-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.f256GarciaStichtenothCanonicalDifferential_selected_residue
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:58:22.954353+00:00
-- url     : https://prove2.me/submissions/63940c1b-aae2-421a-ae12-cc55604a9166

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureGenus
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SelectedFibreSeparation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWZeroRamification
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWRamification
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ExplicitGarciaStichtenothTower
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceClosureCanonicalDifferential_selected_residue


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
open Filter FunctionFieldDifferential
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution (i : ℕ)
    (j : Fin (f256GarciaStichtenothLength i)) :
    Differential.simplePoleResidue (f256GarciaStichtenothSelectedPlace i j)
      (f256GarciaStichtenothCanonicalDifferentialAtPlace i (f256GarciaStichtenothSelectedPlace i j)) = 1 :=
  sourceClosureCanonicalDifferential_selected_residue (i + 2) j
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
