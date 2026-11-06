-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceBasicReverseRational_rhs_order_dichotomy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:32:23.127168+00:00
-- url     : https://prove2.me/submissions/756dce4b-469c-4da1-81b3-91f0cade6a68

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
    (P : GlobalPlace F256 F256⟮(sourceDistinguishedCoordinate (i + 1))⁻¹⟯) :
    P.order (sourceStepRhs
      (AdjoinSimple.gen F256 ((sourceDistinguishedCoordinate (i + 1))⁻¹))) = -1 ∨
      0 ≤ P.order (sourceStepRhs
        (AdjoinSimple.gen F256 ((sourceDistinguishedCoordinate (i + 1))⁻¹))) := by
  apply sourceBasicRationalSubfield_sourceStepRhs_order_dichotomy _ _ P
  intro halg
  exact sourceBasicSourceCoordinate_transcendental (i + 1)
    (IsAlgebraic.inv_iff.mp halg)
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
