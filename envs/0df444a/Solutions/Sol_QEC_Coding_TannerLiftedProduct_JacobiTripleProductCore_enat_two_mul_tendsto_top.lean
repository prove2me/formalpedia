-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.enat_two_mul_tendsto_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:18:35.381736+00:00
-- url     : https://prove2.me/submissions/5c7dab48-9ba7-4ac5-86b4-14ca324ea197

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution :
    Filter.Tendsto (fun i : ℕ => 2 * (i : ℕ∞)) Filter.atTop (nhds ⊤) := by
  rw [ENat.tendsto_nhds_top_iff_natCast_lt]
  intro n
  filter_upwards [Filter.eventually_ge_atTop (n + 1)] with i hi
  exact ENat.coe_lt_coe.mpr (by nlinarith)
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
