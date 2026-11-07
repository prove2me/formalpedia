-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.order_shifted_tendsto_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:47:13.974905+00:00
-- url     : https://prove2.me/submissions/34b1b5e8-b3f7-4863-82a1-3a6285710432

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_order_q_pow_ge
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_enat_add_two_mul_tendsto_top

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (k : ℕ) :
    Filter.Tendsto (fun n ↦ (q ^ 2 * (q ^ 2) ^ k * (q ^ 2) ^ n).order)
      Filter.atTop (nhds ⊤) := by
  apply tendsto_nhds_top_mono' (f := fun n => ((2 + 2 * k + 2 * n : ℕ) : ℕ∞))
  · exact (enat_add_two_mul_tendsto_top ((2 + 2 * k : ℕ) : ℕ∞)).congr
      (fun n => by push_cast; ring)
  · intro n
    show ((2 + 2 * k + 2 * n : ℕ) : ℕ∞) ≤ (q ^ 2 * (q ^ 2) ^ k * (q ^ 2) ^ n).order
    rw [show q ^ 2 * (q ^ 2) ^ k * (q ^ 2) ^ n = q ^ (2 + 2 * k + 2 * n) by
      rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add]]
    exact order_q_pow_ge _
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
