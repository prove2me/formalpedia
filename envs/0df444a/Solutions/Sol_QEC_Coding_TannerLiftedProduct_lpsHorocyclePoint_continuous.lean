-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsHorocyclePoint_continuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:45:29.719278+00:00
-- url     : https://prove2.me/submissions/94c32a91-2331-4567-9afc-9dba134d2446

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
theorem _root_.solution (y : ℝ) (hy : 0<y) :
    Continuous (lpsHorocyclePoint y hy) := by
  apply continuous_induced_rng.mpr
  change Continuous (fun x : ℝ => (⟨x,y⟩:ℂ))
  have he : (fun x : ℝ => (⟨x,y⟩:ℂ))=(fun x : ℝ => (x:ℂ)+Complex.I*(y:ℂ)) := by
    funext x
    apply Complex.ext <;> simp
  rw [he]
  fun_prop
end QEC.Coding.TannerLiftedProduct
