-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsCuspHorocycleCircle_summable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:45:34.647842+00:00
-- url     : https://prove2.me/submissions/0fd21aca-be90-4449-9f48-cd25ff20f491

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
    (y : ℝ) (hy : 0<y) (x : AddCircle (1:ℝ)) :
    Summable (fun n : ℕ => lpsCuspHorocycleTerm N f y n x) :=
  (lpsWeightTwoCuspHorocycle_coeff_norm_summable N f y hy).of_norm_bounded
    (fun n => (lpsCuspHorocycleTerm_norm N f y n x).le)
end QEC.Coding.TannerLiftedProduct
