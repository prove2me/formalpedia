-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceClosureConjugateW_regularRefinement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:04:59.052013+00:00
-- url     : https://prove2.me/submissions/70089ace-f72b-45b6-93db-02c99c43ac80

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RegularSourceRefinement
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureConjugateChains
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureRegularRefinement
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceClosureConjugateW_valuation_eq_one
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_embeddedSourceW_regularRefinement
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceClosureConjugateW_adjoin


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
    RegularRefinement Q (sourceClosureWBase m) (f.restrictScalars F256).fieldRange := by
  have hbase := sourceClosureConjugateW_adjoin m f
  have hwmem : f (algebraMap (RatFunc F256) (SourceField m) galoisBaseW) ∈ sourceClosureWBase m := by
    rw [← hbase]
    exact mem_adjoin_simple_self F256 _
  have hle : sourceClosureWBase m ≤ (f.restrictScalars F256).fieldRange := by
    rw [← hbase, IntermediateField.adjoin_simple_le_iff]
    exact ⟨_, rfl⟩
  have h := embeddedSourceW_regularRefinement m (f.restrictScalars F256) Q
    (sourceClosureWBase m) hwmem (sourceClosureConjugateW_valuation_eq_one m f Q hw)
  rwa [sup_eq_right.mpr hle] at h
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
