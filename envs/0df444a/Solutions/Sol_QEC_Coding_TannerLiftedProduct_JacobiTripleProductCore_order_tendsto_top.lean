-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.order_tendsto_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:47:56.933922+00:00
-- url     : https://prove2.me/submissions/f13d7e43-87a3-4fe5-b7d2-7b60eeb3f614

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_order_coeff_mul_pow_ge

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution {x : R} (hx : x.constantCoeff = 0) (p : S) :
    Filter.Tendsto (fun n : ℕ => ((p.coeff n) * x ^ n).order) Filter.atTop (nhds ⊤) := by
  rw [ENat.tendsto_nhds_top_iff_natCast_lt]
  intro k
  rw [Filter.eventually_atTop]
  exact ⟨k + 1, fun m hm => lt_of_lt_of_le
    (by exact_mod_cast (by omega : k < m)) (order_coeff_mul_pow_ge hx p m)⟩
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
