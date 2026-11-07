-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.exists_bound_for_order
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:46:49.516312+00:00
-- url     : https://prove2.me/submissions/3fe46fc9-ccf0-42b0-8796-65f8aaa5e7a0

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution
    {f : ℕ → ℕ∞} (hf : Filter.Tendsto f Filter.atTop (nhds ⊤)) (d : ℕ) :
    ∃ N : ℕ, ∀ n, N ≤ n → (d : ℕ∞) < f n :=
  (ENat.tendsto_nhds_top_iff_natCast_lt.mp hf d).exists_forall_of_atTop
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
