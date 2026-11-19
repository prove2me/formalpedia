-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsPrimePowerCusp_denominator_dvd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:40:44.82221+00:00
-- url     : https://prove2.me/submissions/e9f9c4ec-b0af-47ef-a1a6-3bed6d37c64c

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaEisensteinCusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspFactorization

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (p e t L : ℕ) (hp : p.Prime) (hc : p.Coprime L) :
    (p:ℤ)^e∣((p^t*L:ℕ):ℤ) ↔ e≤t := by
  rw [←Nat.cast_pow,Int.ofNat_dvd]
  constructor
  · intro h
    exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp ((hc.pow_left e).dvd_of_dvd_mul_right h)
  · intro h
    exact (pow_dvd_pow p h).trans (dvd_mul_right _ _)
end QEC.Coding.TannerLiftedProduct
