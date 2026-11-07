-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.qBinom_theorem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:49:06.32683+00:00
-- url     : https://prove2.me/submissions/699b040c-e85e-4184-ba35-8e383e5232ea

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_qBinom_theorem_succ

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (A Q : R) (n : ℕ) :
    qPoch A Q n =
    ∑ k ∈ Finset.range (n + 1), qBinom Q n k * (-A) ^ k * Q ^ k.choose 2 := by
  induction n generalizing A with
  | zero => simp [qPoch, qBinom]
  | succ n ih => exact qBinom_theorem_succ A Q n ih
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
