-- Prove2me | solution 1 for P2M_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_neg_A_Q__pow_fc719b7707f4
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:15:04.130068+00:00
-- url     : https://prove2.me/submissions/f7ac1a52-b691-4322-9c06-889da5699fb5

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (j ℓ : ℕ) :
    (-(A_hahn j * Q₀)) ^ ℓ = (-A_hahn j) ^ ℓ * Q₀ ^ ℓ := by ring
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
