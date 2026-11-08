-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.exactPairFactors_of_coarse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:33:58.711691+00:00
-- url     : https://prove2.me/submissions/468dc7d9-1e65-4e12-82f5-6282ad57af9d

import Definitions.Def_QEC_Coding_ExpanderCodes_LocalParameterSelection
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerPairExistence
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lowWeightFactor_le_coarse
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_rectangleFactor_le_coarse


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe u
variable {F G W R R' : Type u}
variable [Field F] [Fintype F]
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_62dc6baf31_23
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_62dc6baf31_24
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (w r r' d m s k q : Nat) (hq : 0 < q)
    (hFirstKernel : 6 * coarseLowWeightFactor w d q < q ^ r)
    (hFirstImage :
      6 * (q ^ r * coarseLowWeightFactor w d q) < q ^ w)
    (hSecondKernel : 6 * coarseLowWeightFactor w d q < q ^ r')
    (hSecondImage :
      6 * (q ^ r' * coarseLowWeightFactor w d q) < q ^ w)
    (hForwardRectangle :
      6 * coarseRectangleFactor w m s q < q ^ (k * r))
    (hReverseRectangle :
      6 * coarseRectangleFactor w m s q < q ^ (k * r')) :
    (6 * (∑ t : Fin d, Nat.choose w t.1 * q ^ t.1) < q ^ r) ∧
    (6 * (q ^ r *
      (∑ t : Fin d, Nat.choose w t.1 * q ^ t.1)) < q ^ w) ∧
    (6 * (∑ t : Fin d, Nat.choose w t.1 * q ^ t.1) < q ^ r') ∧
    (6 * (q ^ r' *
      (∑ t : Fin d, Nat.choose w t.1 * q ^ t.1)) < q ^ w) ∧
    (6 * ((Nat.choose w (w - 2 * m)) ^ 2 *
      (s * (((w - 2 * m) * (w - 2 * m) + 1) ^ s) *
        q ^ (2 * (2 * m) * w + s))) < q ^ (k * r)) ∧
    (6 * ((Nat.choose w (w - 2 * m)) ^ 2 *
      (s * (((w - 2 * m) * (w - 2 * m) + 1) ^ s) *
        q ^ (2 * (2 * m) * w + s))) < q ^ (k * r')) := by
  have hLow := lowWeightFactor_le_coarse w d q hq
  have hRectangle := rectangleFactor_le_coarse w m s q
  constructor
  · exact (Nat.mul_le_mul_left 6 hLow).trans_lt hFirstKernel
  constructor
  · exact (Nat.mul_le_mul_left 6
      (Nat.mul_le_mul_left (q ^ r) hLow)).trans_lt hFirstImage
  constructor
  · exact (Nat.mul_le_mul_left 6 hLow).trans_lt hSecondKernel
  constructor
  · exact (Nat.mul_le_mul_left 6
      (Nat.mul_le_mul_left (q ^ r') hLow)).trans_lt hSecondImage
  constructor
  · exact (Nat.mul_le_mul_left 6 hRectangle).trans_lt hForwardRectangle
  · exact (Nat.mul_le_mul_left 6 hRectangle).trans_lt hReverseRectangle
end QEC.Coding.TannerLiftedProduct
