-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSelectedRestrictedBasePlace_order_X_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:35:22.486879+00:00
-- url     : https://prove2.me/submissions/6d9cbd02-a663-4619-bbfa-4ba02743b687

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceNormalClosure
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSelectedPlaceOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RatFuncPlaceClassification
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSelectedBaseRestriction

set_option autoImplicit false
open Polynomial
open scoped RatFunc WithZero
open MonoidWithZeroHom
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution
    (m : ℕ) (index : SourceSelectedPlaceIndex m) :
    (sourceSelectedRestrictedBasePlace m index).order
        (RatFunc.X - 1) = 1 := by
  unfold GlobalPlace.order sourceSelectedRestrictedBasePlace
  rw [sourceSelectedRestrictedBaseValuation_X_sub_one, WithZero.log_exp]
  norm_num
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
