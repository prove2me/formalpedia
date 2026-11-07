-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.tendsto_sq_enat_atTop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:18:45.100202+00:00
-- url     : https://prove2.me/submissions/5c44e325-c09c-4629-83b3-f9f094a8c4fe

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution :
    Filter.Tendsto (fun k : ℕ => (↑(k ^ 2) : ℕ∞)) Filter.atTop (nhds ⊤) := by
  rw [ENat.tendsto_nhds_top_iff_natCast_lt]
  intro n
  filter_upwards [Filter.eventually_ge_atTop (n + 1)] with k hk
  exact_mod_cast show (n : ℕ) < k ^ 2 by nlinarith
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
