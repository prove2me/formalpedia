-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.log_mul_self_pow_le_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:54:44.214137+00:00
-- url     : https://prove2.me/submissions/63b9eca6-b00c-433d-9722-98916f602667

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerSemanticDistance
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerScheduleBounds
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_self_le_base_pow
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_self_pow_le_base_pow_mul
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_log_le_exponent_of_le_pow

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe u
variable {F G W R R' : Type u}
variable [Field F] [Fintype F]
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_5f18e3d3db_23
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_5f18e3d3db_24
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (q C n a : Nat) (hq : 2 ≤ q) :
    Nat.log q (C * n ^ a) ≤ C + n * a := by
  apply log_le_exponent_of_le_pow q _ _ (by omega)
  calc
    C * n ^ a ≤ q ^ C * q ^ (n * a) :=
      Nat.mul_le_mul (self_le_base_pow q C hq)
        (self_pow_le_base_pow_mul q n a hq)
    _ = q ^ (C + n * a) := by rw [pow_add]
end QEC.Coding.TannerLiftedProduct
