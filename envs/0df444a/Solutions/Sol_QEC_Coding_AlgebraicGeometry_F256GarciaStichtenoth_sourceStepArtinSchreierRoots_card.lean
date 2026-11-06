-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceStepArtinSchreierRoots_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:55:50.558004+00:00
-- url     : https://prove2.me/submissions/e2e00bb2-49b0-48a9-86b9-221d491d6efe

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_GaloisBase
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisStep
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSplitAlgebra
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256ArtinSchreier_ker_card


set_option autoImplicit false
open Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution (a : GaloisBaseSplitPoint) :
    (sourceStepArtinSchreierRoots a).card = 16 := by
  calc
    (sourceStepArtinSchreierRoots a).card =
        Fintype.card ↥(sourceStepArtinSchreierRoots a) :=
      (Fintype.card_coe _).symm
    _ = Fintype.card (LinearMap.ker f256ArtinSchreier) :=
      Fintype.card_congr (sourceStepArtinSchreierKernelEquivRoots a).symm
    _ = 16 := f256ArtinSchreier_ker_card
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
