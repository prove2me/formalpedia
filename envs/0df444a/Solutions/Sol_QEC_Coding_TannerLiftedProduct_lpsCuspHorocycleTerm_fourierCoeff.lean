-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsCuspHorocycleTerm_fourierCoeff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:17:53.474213+00:00
-- url     : https://prove2.me/submissions/5fecfb26-6eab-4686-a487-dc97355c8051

import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.NumberTheory.ModularForms.Bounds
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHorocycle
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHorocyclePoint_im
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHorocyclePoint_im

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology MeasureTheory Asymptotics
open scoped MatrixGroups UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (y : ℝ) (n : ℕ) (k : ℤ) :
    fourierCoeff (lpsCuspHorocycleTerm N f y n) k=
      if (n:ℤ)=k then PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 f)*
        ((Real.exp (-2*Real.pi*y):ℂ)^n) else 0 := by
  unfold lpsCuspHorocycleTerm
  rw [fourierCoeff.const_mul,fourierCoeff_fourier]
  by_cases h : (n:ℤ)=k
  · subst k
    simp
  · have h' : k≠(n:ℤ) := fun he => h he.symm
    simp [h,h']
end QEC.Coding.TannerLiftedProduct
