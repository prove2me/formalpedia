-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsCuspHorocycleCircle_continuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:07:31.61966+00:00
-- url     : https://prove2.me/submissions/32b12689-4271-47fb-b7e9-e1a19bac2cb6

import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.NumberTheory.ModularForms.Bounds
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHorocycle
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsWeightTwoCuspHorocycle_coeff_norm_summable
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspHorocycleTerm_norm

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology MeasureTheory Asymptotics
open scoped MatrixGroups UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (y : ℝ) (hy : 0<y) : Continuous (lpsCuspHorocycleCircle N f y) := by
  apply continuous_tsum (fun n => ?_) (lpsWeightTwoCuspHorocycle_coeff_norm_summable N f y hy)
    (fun n x => (lpsCuspHorocycleTerm_norm N f y n x).le)
  unfold lpsCuspHorocycleTerm
  exact continuous_const.mul (map_continuous (fourier (n:ℤ)))
end QEC.Coding.TannerLiftedProduct
