-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.AffinePlace.order_lowerBound_iff_valuation_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:12:20.965207+00:00
-- url     : https://prove2.me/submissions/33f02052-a3bf-4ccb-a2aa-4a9ea3dfdb13

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_AffinePrincipalDivisor
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_AffineCountBridge

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc WithZero nonZeroDivisors
open QEC.Coding.AlgebraicGeometry.AffinePlace
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.AffinePlace._p2m_local_instance_45ffe40864_30
namespace QEC.Coding.AlgebraicGeometry.AffinePlace
theorem _root_.solution (P : carrier k F) {f : F} (hf : f ≠ 0)
    (n : ℤ) :
    -n ≤ GlobalPlace.order (globalPlace k F P) f ↔
      valuation k F P f ≤ WithZero.exp n := by
  change -n ≤ -WithZero.log (valuation k F P f) ↔
    valuation k F P f ≤ WithZero.exp n
  rw [neg_le_neg_iff]
  exact WithZero.log_le_iff_le_exp ((valuation k F P).ne_zero_iff.mpr hf)
end QEC.Coding.AlgebraicGeometry.AffinePlace
