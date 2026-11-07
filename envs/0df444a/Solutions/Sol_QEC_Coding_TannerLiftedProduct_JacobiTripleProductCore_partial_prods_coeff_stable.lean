-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.partial_prods_coeff_stable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:47:36.666934+00:00
-- url     : https://prove2.me/submissions/d5453759-f1de-407d-962d-6f4ba47c1af0

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_qPoch_split
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_coeff_mul_of_trunc_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_tail_coeff_eq_ite

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (x : R) (m n n' : ℕ) (hmn : m < n) (hnn' : n ≤ n') :
    (qPoch (-x * q) (q ^ 2) n' : R).coeff m =
    (qPoch (-x * q) (q ^ 2) n : R).coeff m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnn'
  rw [qPoch_split]
  exact coeff_mul_of_trunc_one _ _ m (tail_coeff_eq_ite x m n k hmn)
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
