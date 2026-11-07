-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.natAbs_sq_add_tendsto_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:14:28.723458+00:00
-- url     : https://prove2.me/submissions/3b42074a-3132-437f-a174-78b240f279bd

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_tendsto_natCast_enat_atTop

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (j : ℕ) :
    Filter.Tendsto (fun ℓ : ℕ => ((-(↑j + 1 : ℤ) + ↑ℓ).natAbs ^ 2 + ℓ : ℕ∞))
      Filter.atTop (nhds ⊤) :=
  tendsto_nhds_top_mono' tendsto_natCast_enat_atTop fun ℓ =>
    show (ℓ : ℕ∞) ≤ _ by exact_mod_cast show ℓ ≤ (-(↑j + 1 : ℤ) + ↑ℓ).natAbs ^ 2 + ℓ by omega
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
