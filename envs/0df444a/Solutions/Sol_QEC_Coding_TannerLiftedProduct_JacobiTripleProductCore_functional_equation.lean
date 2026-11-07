-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.functional_equation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:58:26.765881+00:00
-- url     : https://prove2.me/submissions/68309368-06e2-47c1-8658-b31b84f459c5

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_coeff_A_hahn_mul
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_E_coeff_eq_telescope

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (j : ℕ) (b : ℤ) :
    E_coeff (A_hahn j) b =
    E_coeff (A_hahn j * Q₀) b - E_coeff (A_hahn j * Q₀) (b + (2 * ↑j)) := by
  rw [E_coeff_eq_telescope]
  congr 1
  show ∑ᶠ ℓ : ℕ, (A_hahn j * ((-(A_hahn j * Q₀)) ^ ℓ * Q₀ ^ (ℓ.choose 2) * V ℓ)).coeff b =
    E_coeff (A_hahn j * Q₀) (b + (2 * ↑j))
  simp_rw [coeff_A_hahn_mul]
  rfl
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
