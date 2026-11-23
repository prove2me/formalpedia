-- Prove2me | solution 1 for SumProduct.volume_convexBodyLT_const
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:51:23.795825+00:00
-- url     : https://prove2.me/submissions/d36227b8-fc1e-4da3-a797-0dcacf8abb8f

import Definitions.Def_SumProduct_Boxes
import Definitions.Def_SumProduct_AdditiveCount

set_option autoImplicit true
open scoped NumberField
open Pointwise
open SumProduct
open scoped Classical
open MeasureTheory NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
namespace SumProduct
theorem _root_.solution {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] {d : ℕ} (hd : Module.finrank ℚ K = d) (r : NNReal) :
    volume (convexBodyLT K (fun _ => r)) = (2 : ENNReal) ^ d * (r : ENNReal) ^ d := by
  have h0 : nrComplexPlaces K = 0 := IsTotallyReal.nrComplexPlaces_eq_zero (K := K)
  have hr : nrRealPlaces K = d := by
    have h := card_add_two_mul_card_eq_rank K
    rw [hd, h0] at h; omega
  have hsum : ∑ w : InfinitePlace K, mult w = d := by rw [sum_mult_eq, hd]
  rw [convexBodyLT_volume, convexBodyLTFactor, h0, pow_zero, mul_one, hr,
    Finset.prod_pow_eq_pow_sum, hsum, ENNReal.coe_pow]
  norm_num
end SumProduct
