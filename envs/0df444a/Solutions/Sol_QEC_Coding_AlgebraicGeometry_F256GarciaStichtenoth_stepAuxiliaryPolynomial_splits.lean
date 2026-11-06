-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepAuxiliaryPolynomial_splits
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:01:46.51364+00:00
-- url     : https://prove2.me/submissions/d31367e6-bd49-47a6-b76e-6ade0e986666

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_AuxiliaryMinpoly
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ResidualPolynomial
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepAuxiliaryPolynomial_roots
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256ArtinSchreierRoots_card
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepAuxiliaryPolynomial_natDegree
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepAuxiliaryPolynomial_natDegree



set_option autoImplicit false
open Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution (a : F256) :
    (stepAuxiliaryPolynomial a).Splits := by
  rw [Polynomial.splits_iff_card_roots, stepAuxiliaryPolynomial_roots,
    Finset.card_val, f256ArtinSchreierRoots_card,
    stepAuxiliaryPolynomial_natDegree]
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
