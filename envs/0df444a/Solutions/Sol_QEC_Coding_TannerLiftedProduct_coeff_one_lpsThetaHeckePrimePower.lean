-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.coeff_one_lpsThetaHeckePrimePower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:27:42.909199+00:00
-- url     : https://prove2.me/submissions/79011157-b554-4df3-a0c5-d19b50418a0d

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspidalRemainder
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaHecke
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_one_lpsHeckePrimePowerLinearMap


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (p : ℕ) (a : LPSResiduePrime p) (r : ℕ) :
    PowerSeries.coeff 1 (UpperHalfPlane.qExpansion 1 (lpsThetaHeckePrimePower p a r))=
      PowerSeries.coeff (p^r) (UpperHalfPlane.qExpansion 1 (lpsThetaCuspidalRemainder a.q a.modFour)) := by
  let : Fact p.Prime := ⟨a.degreePrime⟩
  unfold lpsThetaHeckePrimePower
  exact coeff_one_lpsHeckePrimePowerLinearMap _ p _ r _
end QEC.Coding.TannerLiftedProduct
