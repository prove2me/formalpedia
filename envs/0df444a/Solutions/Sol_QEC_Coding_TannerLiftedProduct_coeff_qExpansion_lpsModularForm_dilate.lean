-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.coeff_qExpansion_lpsModularForm_dilate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:16:59.507111+00:00
-- url     : https://prove2.me/submissions/936016fc-90e3-442b-b3a3-72f9d91e32bb

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSIteratedEisenstein
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEisensteinDifference
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsModularForm_dilate_hasSum
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2TwistModularForm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsQuadraticE2TwistModularForm_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N m : ℕ) [NeZero N] (hm : 0 < m)
    (f : ModularForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) (n : ℕ) :
    PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 (lpsModularForm_dilate N m hm f))=
      lpsModularDilationCoefficient
        (fun k => PowerSeries.coeff k (UpperHalfPlane.qExpansion 1 f)) m n := by
  have hp : (1:ℝ) ∈ (CongruenceSubgroup.Gamma0 (N*m) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by simp
  symm
  exact ModularFormClass.qExpansion_coeff_unique (by norm_num : (0:ℝ)<1) hp
    (fun z => by simpa only [smul_eq_mul] using lpsModularForm_dilate_hasSum N m hm f z) n
end QEC.Coding.TannerLiftedProduct
