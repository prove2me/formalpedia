-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.quadraticArtinSchreierTowerStep_finrank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:00:33.826041+00:00
-- url     : https://prove2.me/submissions/9b566bb7-4952-4eb2-a85c-f3ad61089fc3

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticStepDifferent
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticTower
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_quadraticArtinSchreier_finrank


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
universe u
variable {K : Type u} [Field K] [Algebra F256 K]
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) (i : ℕ) :
    Module.finrank
      (QuadraticArtinSchreierTowerField P a ha i)
      (QuadraticArtinSchreierTowerField P a ha (i + 1)) = 2 :=
  quadraticArtinSchreier_finrank
    (quadraticArtinSchreierTowerPlace P a ha i)
    (quadraticArtinSchreierTowerCoordinate P a ha i)
    (quadraticArtinSchreierTowerCoordinate_order P a ha i)
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
