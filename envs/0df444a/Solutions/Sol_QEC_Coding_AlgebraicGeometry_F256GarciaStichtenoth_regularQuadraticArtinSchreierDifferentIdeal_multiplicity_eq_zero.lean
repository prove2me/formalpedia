-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.regularQuadraticArtinSchreierDifferentIdeal_multiplicity_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:31:26.510309+00:00
-- url     : https://prove2.me/submissions/c1f5dfc3-40e4-4e31-94d9-b9b70869f460

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticStepDifferent
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RegularQuadraticStep
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_regularQuadraticArtinSchreierDifferentIdeal_eq_top

set_option autoImplicit false
open Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution
    (P : GlobalPlace F256 K) (b : P.valuationRing)
    (hirr : Irreducible (regularQuadraticArtinSchreierPolynomial P b)) :
    multiplicity (regularQuadraticArtinSchreierUpperIdeal P b hirr)
        (differentIdeal P.valuationRing
          (RegularQuadraticArtinSchreierIntegralClosure P b hirr)) = 0 := by
  rw [regularQuadraticArtinSchreierDifferentIdeal_eq_top]
  apply multiplicity_eq_zero.mpr
  rw [Ideal.dvd_iff_le]
  intro htop
  exact (regularQuadraticArtinSchreierUpperIdeal_isMaximal P b hirr).ne_top
    (top_unique htop)
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
