-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceClosureConjugateW_valuation_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:45:13.541367+00:00
-- url     : https://prove2.me/submissions/ac1b9bf4-8180-4d36-a89d-c9a11551739f

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RegularSourceRefinement
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureConjugateChains
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureRegularRefinement
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWClosureGenerator_pow_fifteen


set_option autoImplicit false
open IntermediateField
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
attribute [local instance] sourceConstantBaseTower
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution (m : ℕ)
    (f : SourceField m →ₐ[GaloisBaseField] SourceGaloisClosureField m)
    (Q : GlobalPlace F256 (SourceGaloisClosureField m))
    (hw : Q.valuation (sourceGaloisWClosureGenerator m : SourceGaloisClosureField m) = 1) :
    Q.valuation (f (algebraMap (RatFunc F256) (SourceField m) galoisBaseW)) = 1 := by
  have hp : (algebraMap (RatFunc F256) (SourceField m) galoisBaseW) ^ 15 =
      algebraMap GaloisBaseField (SourceField m) (AdjoinSimple.gen F256 galoisBaseZ) := by
    rw [← map_pow]
    rfl
  have hpow : f (algebraMap (RatFunc F256) (SourceField m) galoisBaseW) ^ 15 =
      (sourceGaloisWClosureGenerator m : SourceGaloisClosureField m) ^ 15 := by
    rw [← map_pow, hp, f.commutes, sourceGaloisWClosureGenerator_pow_fifteen]
  have h := congrArg Q.valuation hpow
  rw [map_pow, map_pow, hw, one_pow] at h
  exact (pow_eq_one_iff_of_nonneg zero_le (by norm_num : (15 : ℕ) ≠ 0)).mp h
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
