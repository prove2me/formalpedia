-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsThetaEisenstein_chi4_cusp_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:42:56.369207+00:00
-- url     : https://prove2.me/submissions/044efe7e-5304-459c-b6a2-6e0fab5b13cd

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaEisensteinCorrection
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspLocalFactors
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaEisensteinCusps
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsThetaEisensteinChi4Weight_scaled

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q : ℕ) [Fact q.Prime] (γ : SL(2,ℤ)) :
    (∑ b : Fin 3,lpsThetaEisensteinChi4Weight q b*
      ((Int.gcd ((q^b.val:ℕ):ℤ) (γ 1 0):ℂ)^2/((q^b.val:ℕ):ℂ)^2))=
      -lpsThetaEisensteinPrimeCuspFactor q γ := by
  have he (b : Fin 3) : lpsThetaEisensteinChi4Weight q b*
      ((Int.gcd ((q^b.val:ℕ):ℤ) (γ 1 0):ℂ)^2/((q^b.val:ℕ):ℂ)^2)=
      -(lpsThetaEisensteinPrimeWeight q b*(Int.gcd ((q^b.val:ℕ):ℤ) (γ 1 0):ℂ)^2/
        ((q^b.val:ℕ):ℂ)) := by
    calc
      _=(lpsThetaEisensteinChi4Weight q b/((q^b.val:ℕ):ℂ)^2)*
        (Int.gcd ((q^b.val:ℕ):ℤ) (γ 1 0):ℂ)^2 := by ring
      _=_ := by rw [lpsThetaEisensteinChi4Weight_scaled];ring
  simp_rw [he]
  rw [Finset.sum_neg_distrib]
  rfl
end QEC.Coding.TannerLiftedProduct
