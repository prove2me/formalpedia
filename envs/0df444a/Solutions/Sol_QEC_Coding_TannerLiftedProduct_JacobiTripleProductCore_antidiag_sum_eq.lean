-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.antidiag_sum_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:18:39.44537+00:00
-- url     : https://prove2.me/submissions/3c3991d5-3312-4cdc-9482-7b455c93ab1d

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (f g : R) (m : ℕ)
    (hg : ∀ j ≤ m, g.coeff j = if j = 0 then 1 else 0) :
    ∑ p ∈ Finset.HasAntidiagonal.antidiagonal m,
      f.coeff p.1 * g.coeff p.2 = f.coeff m := by
  rw [Finset.sum_eq_single_of_mem (m, 0)
    (Finset.HasAntidiagonal.mem_antidiagonal.mpr (add_zero m))
    (fun b hb hne => ?_)]
  · simp [hg 0 (Nat.zero_le m)]
  · have hb_sum := Finset.HasAntidiagonal.mem_antidiagonal.mp hb
    rw [hg b.2 (by omega), if_neg (fun h => hne (by ext <;> simp_all)), mul_zero]
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
