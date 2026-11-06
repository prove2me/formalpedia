-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceStepRhs_mem_sourceSeedIntegralClosure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:35:37.963198+00:00
-- url     : https://prove2.me/submissions/a0401362-fc45-45ac-8bba-d62323f7b54a

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSelectedBaseRestriction
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_StepPlaceTransport
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Valuation.LocalSubring
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSeedSplittingIdeals
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceSeedIntegralClosure_exists_of_regularAt_selected
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceSelectedRationalPlace_coordinate_split


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSeedBaseValuationRingBaseModule
attribute [local instance 2000] sourceSeedBaseValuationRingBaseModule
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSeedBaseValuationRingBaseFaithfulSMul
attribute [local instance 2000] sourceSeedBaseValuationRingBaseFaithfulSMul
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSeedBaseValuationRingAlgebra
attribute [local instance 2000] sourceSeedBaseValuationRingAlgebra
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSeedBaseValuationRingSMul
attribute [local instance 2000] sourceSeedBaseValuationRingSMul
attribute [local instance 2000] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSeedBaseValuationRingModule
attribute [local instance 2000] sourceSeedBaseValuationRingModule
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSeedBaseScalarTower
attribute [local instance] sourceSeedBaseScalarTower
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSeedIntegralClosureTorsionFree
attribute [local instance] sourceSeedIntegralClosureTorsionFree
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSeedIntegralClosureFinite
attribute [local instance] sourceSeedIntegralClosureFinite
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSeedIntegralClosureIsFractionRing
attribute [local instance] sourceSeedIntegralClosureIsFractionRing
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSeedIntegralClosureIsDedekind
attribute [local instance] sourceSeedIntegralClosureIsDedekind
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution (m : ℕ) :
    ∃ xO : SourceSeedIntegralClosure m,
      algebraMap (SourceSeedIntegralClosure m) (SourceField m) xO =
        sourceStepRhs (sourceDistinguishedCoordinate m) := by
  apply sourceSeedIntegralClosure_exists_of_regularAt_selected
  intro index
  exact sourceStepRhs_regularAt_of_splitValue
    (sourceSelectedRationalPlace m index)
    (sourceDistinguishedCoordinate m)
    (sourceSelectedRationalPlace_coordinate_regular m index)
    (sourceSelectedRationalPlace_coordinate_split m index)
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
