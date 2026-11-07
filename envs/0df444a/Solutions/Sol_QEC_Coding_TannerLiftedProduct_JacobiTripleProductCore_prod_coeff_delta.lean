-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.prod_coeff_delta
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:21:51.207868+00:00
-- url     : https://prove2.me/submissions/68200924-3a61-4020-a7a4-567d99449e69

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_coeff_mul_of_trunc_one

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (m : ℕ) (f : ℕ → R) (k : ℕ)
    (hf : ∀ i < k, ∀ j ≤ m, (f i).coeff j = if j = 0 then 1 else 0)
    (j : ℕ) (hj : j ≤ m) :
    (∏ i ∈ Finset.range k, f i).coeff j = if j = 0 then 1 else 0 := by
  induction k with
  | zero => simp [PowerSeries.coeff_one]
  | succ k ih =>
    rw [Finset.prod_range_succ,
      coeff_mul_of_trunc_one _ _ j (fun j' hj' => hf k (Nat.lt_succ_self k) j' (le_trans hj' hj))]
    exact ih (fun i hi j' hj' => hf i (Nat.lt_succ_of_lt hi) j' hj')
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
