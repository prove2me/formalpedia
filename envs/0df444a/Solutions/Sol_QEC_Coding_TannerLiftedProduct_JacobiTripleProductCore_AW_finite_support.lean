-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.AW_finite_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:53:29.999109+00:00
-- url     : https://prove2.me/submissions/91866d06-8e0e-4af2-ad81-bae783becbda

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_coeff_A_hahn_mul
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_W_finite_support

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (j : ℕ) (b : ℤ) :
    (Function.support (fun ℓ : ℕ ↦ (A_hahn j * ((-(A_hahn j * Q₀)) ^ ℓ * Q₀ ^ (ℓ.choose 2) * V ℓ)).coeff b)).Finite :=
  (W_finite_support j (b + 2 * ↑j)).subset fun ℓ hℓ => by
    simp only [Function.mem_support] at hℓ ⊢; rwa [coeff_A_hahn_mul] at hℓ
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
