-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.eval_x_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:53:44.726488+00:00
-- url     : https://prove2.me/submissions/f3c80c4c-76e4-4185-9153-118cd4cf6a54

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_instIsTopologicalSemiringPiTop
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_summable_eval_series
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_piTop_T3
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_summable_product_term

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (x : R) (hx : x.constantCoeff = 0) (p q : S) :
    eval_x_fun x (p * q) = eval_x_fun x p * eval_x_fun x q := by
  show (letI := piTop; ∑' n, (p * q).coeff n * x ^ n) =
    (letI := piTop; ∑' n, p.coeff n * x ^ n) * (letI := piTop; ∑' n, q.coeff n * x ^ n)
  letI : TopologicalSpace R := piTop
  haveI : T3Space R := piTop_T3
  haveI : IsTopologicalSemiring R := instIsTopologicalSemiringPiTop
  rw [(summable_eval_series hx p).tsum_mul_tsum_eq_tsum_sum_antidiagonal
    (summable_eval_series hx q) (summable_product_term hx p q)]
  apply tsum_congr
  intro n
  have hsimpl : ∀ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
      (p.coeff kl.1 * x ^ kl.1) * (q.coeff kl.2 * x ^ kl.2) =
      (p.coeff kl.1 * q.coeff kl.2) * x ^ n := fun kl hkl => by
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hkl
    subst hkl
    rw [pow_add]
    ring
  rw [Finset.sum_congr rfl hsimpl, ← Finset.sum_mul, PowerSeries.coeff_mul]
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
