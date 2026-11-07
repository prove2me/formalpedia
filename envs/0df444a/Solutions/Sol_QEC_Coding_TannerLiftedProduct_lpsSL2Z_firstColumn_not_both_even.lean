-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsSL2Z_firstColumn_not_both_even
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:52:50.366102+00:00
-- url     : https://prove2.me/submissions/21cbeb12-e217-4834-bccc-96911bac2055

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCharacterEisensteinCusps
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsSL2Z_firstColumn_gcd_one

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (γ : SL(2,ℤ)) :
    ¬((2:ℤ)∣γ 0 0 ∧ (2:ℤ)∣γ 1 0) := by
  intro h
  have hg := Int.dvd_gcd h.1 h.2
  rw [lpsSL2Z_firstColumn_gcd_one] at hg
  norm_num at hg
end QEC.Coding.TannerLiftedProduct
