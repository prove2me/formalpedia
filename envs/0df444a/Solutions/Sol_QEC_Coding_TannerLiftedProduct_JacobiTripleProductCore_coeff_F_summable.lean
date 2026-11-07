-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.coeff_F_summable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:53:39.088166+00:00
-- url     : https://prove2.me/submissions/fbe3302a-3b08-4bd3-88ab-40d681eacb6f

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_support_finset_Z_nat
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_coeff_F_vanishes

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (d : ℕ) : letI := piTop;
    Summable (fun (p : ℤ × ℕ) => (PowerSeries.coeff d) (F p)) := by
  letI := piTop; obtain ⟨S_fin, hS⟩ := support_finset_Z_nat d
  exact summable_of_ne_finset_zero (s := S_fin) fun ⟨z, ℓ⟩ hzl =>
    coeff_F_vanishes z ℓ d (by contrapose! hzl; exact hS z ℓ hzl)
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
