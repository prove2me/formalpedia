-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.quadraticArtinSchreierTower_equation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:00:24.633543+00:00
-- url     : https://prove2.me/submissions/2fbd528b-c3c8-4c4c-b81f-8fba8aacba03

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticStepDifferent
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticTower
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_quadraticArtinSchreierCoordinate_equation


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
universe u
variable {K : Type u} [Field K] [Algebra F256 K]
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) (i : ℕ) :
    quadraticArtinSchreierTowerCoordinate P a ha (i + 1) ^ 2 +
        quadraticArtinSchreierTowerCoordinate P a ha (i + 1) =
      quadraticArtinSchreierTowerEmbedding P a ha i
        (quadraticArtinSchreierTowerCoordinate P a ha i) :=
  quadraticArtinSchreierCoordinate_equation
    (quadraticArtinSchreierTowerPlace P a ha i)
    (quadraticArtinSchreierTowerCoordinate P a ha i)
    (quadraticArtinSchreierTowerCoordinate_order P a ha i)
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
