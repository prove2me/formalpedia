-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsNatGcd_same_base_powers
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:47:11.17016+00:00
-- url     : https://prove2.me/submissions/fcb79b46-9b38-4cfe-86e2-68667c4c17ea

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaEisensteinCusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspFactorization

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (p a t : ℕ) : Nat.gcd (p^a) (p^t)=p^(min a t) := by
  rcases le_total a t with h | h
  · rw [min_eq_left h]
    exact Nat.gcd_eq_left_iff_dvd.mpr (pow_dvd_pow p h)
  · rw [min_eq_right h]
    exact Nat.gcd_eq_right_iff_dvd.mpr (pow_dvd_pow p h)
end QEC.Coding.TannerLiftedProduct
