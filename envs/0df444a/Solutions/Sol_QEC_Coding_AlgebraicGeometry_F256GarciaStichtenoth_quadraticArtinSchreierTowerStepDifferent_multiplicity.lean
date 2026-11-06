-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.quadraticArtinSchreierTowerStepDifferent_multiplicity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:31:01.088659+00:00
-- url     : https://prove2.me/submissions/12304a88-78b1-4ada-93f8-217bc219cd5f

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticStepDifferent
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticTower
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_quadraticArtinSchreierDifferentIdeal_multiplicity


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
universe u
variable {K : Type u} [Field K] [Algebra F256 K]
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution
    (P : GlobalPlace F256 K) (a : K) (ha : P.order a = -1) (i : ℕ) :
    multiplicity
        (quadraticArtinSchreierUpperIdeal
          (quadraticArtinSchreierTowerPlace P a ha i)
          (quadraticArtinSchreierTowerCoordinate P a ha i)
          (quadraticArtinSchreierTowerCoordinate_order P a ha i))
        (differentIdeal
          (quadraticArtinSchreierTowerPlace P a ha i).valuationRing
          (QuadraticArtinSchreierIntegralClosure
            (quadraticArtinSchreierTowerPlace P a ha i)
            (quadraticArtinSchreierTowerCoordinate P a ha i)
            (quadraticArtinSchreierTowerCoordinate_order P a ha i))) = 2 :=
  quadraticArtinSchreierDifferentIdeal_multiplicity
    (quadraticArtinSchreierTowerPlace P a ha i)
    (quadraticArtinSchreierTowerCoordinate P a ha i)
    (quadraticArtinSchreierTowerCoordinate_order P a ha i)
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
