-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.summable_product_term
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:51:40.982308+00:00
-- url     : https://prove2.me/submissions/3f11cd64-6ae9-441e-82de-f4840c6e15a1

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_summable_coeff_product_term

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution {x : R} (hx : x.constantCoeff = 0) (p q : S) :
    letI := piTop;
    Summable (fun (kl : ℕ × ℕ) => (p.coeff kl.1 * x ^ kl.1) * (q.coeff kl.2 * x ^ kl.2)) := by
  letI := piTop
  rw [PowerSeries.WithPiTopology.summable_iff_summable_coeff]
  intro d
  exact summable_coeff_product_term hx p q d
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
