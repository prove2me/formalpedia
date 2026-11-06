-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.AffinePlace.globalPlace_order_of_integral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:11:50.824987+00:00
-- url     : https://prove2.me/submissions/9b03cb31-9675-4536-a81d-8777079f0403

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AffinePlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_GlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AffineGlobalPlace
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_AffinePlace_valuation_algebraMap_of_integral


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc WithZero
open QEC.Coding.AlgebraicGeometry.AffinePlace
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.AffinePlace._p2m_local_instance_439b1c180e_47
namespace QEC.Coding.AlgebraicGeometry.AffinePlace
theorem _root_.solution (P : carrier k F)
    (x : _root_.FunctionField.ringOfIntegers k F) :
    GlobalPlace.order (globalPlace k F P)
      (algebraMap (_root_.FunctionField.ringOfIntegers k F) F x) =
        -WithZero.log (P.intValuation x) := by
  change -WithZero.log
    (valuation k F P (algebraMap (_root_.FunctionField.ringOfIntegers k F) F x)) = _
  rw [valuation_algebraMap_of_integral k F P x]
end QEC.Coding.AlgebraicGeometry.AffinePlace
