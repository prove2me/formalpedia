-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsGamma0_pos_lower_dvd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T00:19:09.697593+00:00
-- url     : https://prove2.me/submissions/54f0c397-408d-4d06-921a-700ac63df3de

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaFourier
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaGaussScalar

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Real
open scoped UpperHalfPlane ModularForm MatrixGroups
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) (γ : SL(2,ℤ))
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) (hc : 0 < γ 1 0) : N ∣ (γ 1 0).toNat := by
  apply Int.natCast_dvd_natCast.mp
  rw [Int.toNat_of_nonneg hc.le]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (CongruenceSubgroup.Gamma0_mem.mp hγ)
end QEC.Coding.TannerLiftedProduct
