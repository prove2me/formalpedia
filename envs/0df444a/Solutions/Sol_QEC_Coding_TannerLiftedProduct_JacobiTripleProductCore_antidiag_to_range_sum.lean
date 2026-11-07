-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.antidiag_to_range_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:46:35.885579+00:00
-- url     : https://prove2.me/submissions/896c1030-5501-43fa-8ad2-3a240d77b320

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution {n : ℕ} :
    ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, aCoeff p.1 * bCoeff p.2 =
    ∑ k ∈ Finset.range (n + 1), aCoeff (n - k) * bCoeff k := by
  have h1 : ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, aCoeff p.1 * bCoeff p.2 =
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, aCoeff p.2 * bCoeff p.1 :=
    Finset.Nat.sum_antidiagonal_swap (f := fun p => aCoeff p.2 * bCoeff p.1)
  rw [h1]
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => aCoeff b * bCoeff a) n
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
