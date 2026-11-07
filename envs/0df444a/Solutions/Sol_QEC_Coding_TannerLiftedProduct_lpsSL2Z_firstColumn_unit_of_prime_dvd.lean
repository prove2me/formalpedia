-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsSL2Z_firstColumn_unit_of_prime_dvd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:53:12.973199+00:00
-- url     : https://prove2.me/submissions/11bcf3e4-5856-4013-b16a-54437e9442cf

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCharacterEisensteinCusps
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsSL2Z_firstColumn_gcd_one

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q : ℕ) [Fact q.Prime]
    (γ : SL(2,ℤ)) (hC : (q:ℤ)∣γ 1 0) : (γ 0 0:ZMod q)≠0 := by
  intro hz
  have hA := (ZMod.intCast_zmod_eq_zero_iff_dvd (γ 0 0) q).mp hz
  have hg := Int.dvd_gcd hA hC
  rw [lpsSL2Z_firstColumn_gcd_one] at hg
  exact (Fact.out : q.Prime).not_dvd_one hg
end QEC.Coding.TannerLiftedProduct
