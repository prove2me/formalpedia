-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.coeff_qExpansion_lpsThetaCuspidalRemainder_even_power
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:50:45.608179+00:00
-- url     : https://prove2.me/submissions/d1823815-500f-41b5-975f-9de9e3aa28de

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspFactorization
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaModularForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularTraceBridge
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspidalRemainder
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_qExpansion_lpsThetaCuspidalRemainder
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_qExpansion_lpsThetaEisensteinCorrection
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_qExpansion_lpsThetaEisensteinCorrection_even_power


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (p q : ℕ) [Fact q.Prime]
    (hq4 : q%4=1) (hp : Odd p) (hpq : ¬q∣p) (n : ℕ) :
    PowerSeries.coeff (p^(2*n)) (UpperHalfPlane.qExpansion 1 (lpsThetaCuspidalRemainder q hq4))=
      ((PowerSeries.coeff (p^(2*n)) (lpsTraceThetaSeries q):ℕ):ℂ)-
        4*(ArithmeticFunction.sigma 1 (p^(2*n)):ℂ)/((q:ℂ)*((q:ℂ)^2-1)) := by
  rw [coeff_qExpansion_lpsThetaCuspidalRemainder]
  have h := coeff_qExpansion_lpsThetaEisensteinCorrection_even_power p q
    (by intro h;subst q;norm_num at hq4) hp hpq n
  rw [coeff_qExpansion_lpsThetaEisensteinCorrection] at h
  rw [h]
end QEC.Coding.TannerLiftedProduct
