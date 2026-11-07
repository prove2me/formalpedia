-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.tendsto_natCast_enat_atTop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:12:12.284551+00:00
-- url     : https://prove2.me/submissions/1b2e6581-f6c4-473d-86b8-004692b5edf6

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution :
    Filter.Tendsto (fun n : ℕ => (n : ℕ∞)) Filter.atTop (nhds ⊤) := by
  rw [ENat.tendsto_nhds_top_iff_natCast_lt]
  intro n
  filter_upwards [Filter.eventually_ge_atTop (n + 1)] with b hb
  exact ENat.coe_lt_coe.mpr (by omega)
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
