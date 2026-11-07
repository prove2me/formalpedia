-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.split_S2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:18:32.69976+00:00
-- url     : https://prove2.me/submissions/c0698e39-b606-465e-a975-9f2299e5d613

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (A Q : R) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
      qBinom Q n k * (-A) ^ (k + 1) * Q ^ (k + 1).choose 2 =
    (∑ k ∈ Finset.range n,
      qBinom Q n k * (-A) ^ (k + 1) * Q ^ (k + 1).choose 2) +
    (-A) ^ (n + 1) * Q ^ (n + 1).choose 2 := by
  rw [Finset.sum_range_succ]
  simp [qBinom_self]
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
