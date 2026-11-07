-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.qBinom_mul_qPoch
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:48:52.133218+00:00
-- url     : https://prove2.me/submissions/3d7768a2-2782-4f58-99a4-0f226c24e1b3

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_qBinom_mul_qPoch_inductive_step

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (Q : R) (n k : ℕ) (hkn : k ≤ n) :
    qBinom Q n k * qPoch Q Q k * qPoch Q Q (n - k) = qPoch Q Q n := by
  induction n generalizing k with
  | zero =>
    obtain rfl := Nat.le_zero.mp hkn
    simp [qPoch, qBinom]
  | succ n ih =>
    match k, hkn with
    | 0, _ => simp [qBinom, qPoch]
    | k + 1, hkn =>
      have hkn' := Nat.succ_le_succ_iff.mp hkn
      obtain rfl | hk := eq_or_lt_of_le hkn'
      · simp [qBinom_self, qPoch]
      · rw [Nat.succ_sub_succ]
        exact qBinom_mul_qPoch_inductive_step Q n k hk (ih k hk.le) (ih (k + 1) hk)
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
