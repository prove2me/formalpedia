-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.log_self_pow_le_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T11:31:18.466623+00:00
-- url     : https://prove2.me/submissions/e790b4a0-a8aa-47e8-89c3-2e0af9cd013c

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerSemanticDistance
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerScheduleBounds
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
    (q n a : Nat) (hq : 2 ≤ q) :
    Nat.log q (n ^ a) ≤ n * a :=
  log_le_exponent_of_le_pow q (n ^ a) (n * a) (by omega)
    (self_pow_le_base_pow_mul q n a hq)
end QEC.Coding.TannerLiftedProduct
