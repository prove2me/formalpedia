-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsPetersson_complex_strip_inverse_square_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:07:43.737955+00:00
-- url     : https://prove2.me/submissions/da81a82f-02bd-429b-8ac5-3d1a1c83704b

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHorocycle
import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPeterssonMeasure
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsPetersson_im_inverse_square_integrable
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHorocyclePoint_im
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHorocyclePoint_im



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Asymptotics Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ComplexConjugate
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution :
    IntegrableOn (fun z : ℂ => (1/z.im)^2)
      (Complex.measurableEquivRealProd ⁻¹' (Icc (-1/2:ℝ) (1/2) ×ˢ Ioi (1/2:ℝ))) := by
  have hx : IntegrableOn (fun _ : ℝ => (1:ℝ)) (Icc (-1/2:ℝ) (1/2)) :=
    integrableOn_const (C := (1:ℝ)) (by simp)
  have hy := lpsPetersson_im_inverse_square_integrable (1/2) (by norm_num)
  have hp := hx.mul_prod hy
  simp only [one_mul] at hp
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod] at hp
  exact (Complex.volume_preserving_equiv_real_prod.restrict_preimage
    (measurableSet_Icc.prod measurableSet_Ioi)).integrable_comp_emb
      Complex.measurableEquivRealProd.measurableEmbedding |>.mpr hp
end QEC.Coding.TannerLiftedProduct
