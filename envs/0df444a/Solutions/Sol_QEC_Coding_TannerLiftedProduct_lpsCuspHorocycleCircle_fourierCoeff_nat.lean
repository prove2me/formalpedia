-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsCuspHorocycleCircle_fourierCoeff_nat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:08:22.716779+00:00
-- url     : https://prove2.me/submissions/e6227715-f192-4b25-8210-cada638c4653

import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.NumberTheory.ModularForms.Bounds
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHorocycle
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspHorocycleTerm_fourierCoeff
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspHorocycleCircle_fourierCoeff_hasSum

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology MeasureTheory Asymptotics
open scoped MatrixGroups UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (y : ℝ) (hy : 0<y) (n : ℕ) :
    fourierCoeff (lpsCuspHorocycleCircle N f y) (n:ℤ)=
      PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 f)*
        ((Real.exp (-2*Real.pi*y):ℂ)^n) := by
  have h := lpsCuspHorocycleCircle_fourierCoeff_hasSum N f y hy (n:ℤ)
  have he : (fun m : ℕ => fourierCoeff (lpsCuspHorocycleTerm N f y m) (n:ℤ))=
      (fun m : ℕ => if m=n then PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 f)*
        ((Real.exp (-2*Real.pi*y):ℂ)^n) else 0) := by
    funext m
    rw [lpsCuspHorocycleTerm_fourierCoeff]
    by_cases hm : m=n
    · subst m
      rw [if_pos rfl,if_pos rfl]
    · have hm' : (m:ℤ)≠(n:ℤ) := fun hc => hm (Int.ofNat_inj.mp hc)
      rw [if_neg hm',if_neg hm]
  rw [he] at h
  exact HasSum.unique h (hasSum_ite_eq n _)
end QEC.Coding.TannerLiftedProduct
