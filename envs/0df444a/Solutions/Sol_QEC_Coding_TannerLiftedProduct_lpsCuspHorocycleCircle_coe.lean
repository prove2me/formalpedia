-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsCuspHorocycleCircle_coe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:06:12.61851+00:00
-- url     : https://prove2.me/submissions/4dcc2273-8a4e-4cef-a5fd-895abe45be03

import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.NumberTheory.ModularForms.Bounds
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHorocycle
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsWeightTwoCuspHorocycle_hasSum
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHorocyclePoint_qParam
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsFourier_one_pow

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology MeasureTheory Asymptotics
open scoped MatrixGroups UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (y : ℝ) (hy : 0<y) (x : ℝ) :
    lpsCuspHorocycleCircle N f y (x:AddCircle (1:ℝ))=f (lpsHorocyclePoint y hy x) := by
  have h := lpsWeightTwoCuspHorocycle_hasSum N f y hy x
  have he : (fun n : ℕ => PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 f)*
      (Function.Periodic.qParam 1 (lpsHorocyclePoint y hy x:ℂ))^n)=
      (fun n : ℕ => lpsCuspHorocycleTerm N f y n (x:AddCircle (1:ℝ))) := by
    funext n
    rw [lpsHorocyclePoint_qParam,mul_pow,lpsFourier_one_pow]
    unfold lpsCuspHorocycleTerm
    ring
  rw [he] at h
  exact h.tsum_eq
end QEC.Coding.TannerLiftedProduct
