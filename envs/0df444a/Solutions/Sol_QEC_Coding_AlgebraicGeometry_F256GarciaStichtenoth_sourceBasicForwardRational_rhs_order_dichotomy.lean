-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceBasicForwardRational_rhs_order_dichotomy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:32:22.232678+00:00
-- url     : https://prove2.me/submissions/2ee0672c-4970-4a6d-94e2-3cd071c63883

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceRecursion
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_StepPlaceTransport
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_InverseAffinePlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_FixedFieldArtinSchreier
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RationalRecursionOrders
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceBasicSourceCoordinate_transcendental
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceBasicRationalSubfield_sourceStepRhs_order_dichotomy

set_option autoImplicit false
open IntermediateField
open scoped Polynomial RatFunc
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
open scoped BigOperators
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceBasicRationalF256CharTwo
attribute [local instance] sourceBasicRationalF256CharTwo
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution
    (i : ℕ)
    (P : GlobalPlace F256 F256⟮sourceDistinguishedCoordinate i⟯) :
    P.order (sourceStepRhs
      (AdjoinSimple.gen F256 (sourceDistinguishedCoordinate i))) = -1 ∨
      0 ≤ P.order (sourceStepRhs
        (AdjoinSimple.gen F256 (sourceDistinguishedCoordinate i))) :=
  sourceBasicRationalSubfield_sourceStepRhs_order_dichotomy
    (sourceDistinguishedCoordinate i)
    (sourceBasicSourceCoordinate_transcendental i) P
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
