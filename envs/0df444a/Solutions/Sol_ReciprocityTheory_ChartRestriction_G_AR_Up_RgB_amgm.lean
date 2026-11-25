-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.RgB.amgm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:53:40.230583+00:00
-- url     : https://prove2.me/submissions/9419d765-916c-4e04-b0db-58af865a1ae7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustStatementPfA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_DerivDerivNonposOfIsLocalMax
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_LeviVA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_RhGradStatementPfA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_RgB_exists_factor
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_RgB_amgm_psd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExhA_det_eq_ofReal
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExhA_det_re_pos_im
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_re


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.RgB
open Matrix
open scoped ComplexOrder Matrix
open ReciprocityTheory.ChartRestriction.G.AR.Up.ExhA
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.RgB
theorem _root_.solution {m : ℕ} (hm : 0 < m) {A A0 : Matrix (Fin m) (Fin m) ℂ} (hA : A.PosDef)
    (hA0 : A0.PosDef) :
    A.det.re ^ ((m : ℝ)⁻¹) ≤ A0.det.re ^ ((m : ℝ)⁻¹) * ((A * A0⁻¹).trace.re / m) := by
  have hM : (A0⁻¹).PosDef := hA0.inv
  obtain ⟨y, hy⟩ := exists_factor hM.posSemidef
  have hP : (y * A * yᴴ).PosSemidef := hA.posSemidef.mul_mul_conjTranspose_same y
  have htr : (y * A * yᴴ).trace = (A * A0⁻¹).trace := by
    rw [hy, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
  obtain ⟨ha, hai⟩ := det_re_pos_im hA
  obtain ⟨hb, hbi⟩ := det_re_pos_im hA0
  have hdet : (y * A * yᴴ).det.re = A.det.re * (A0.det.re)⁻¹ := by
    have e1 : (y * A * yᴴ).det = A.det * (A0⁻¹).det := by
      rw [hy, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose]; ring
    rw [e1, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', det_eq_ofReal hA, det_eq_ofReal hA0]
    simp only [Complex.ofReal_re]
    rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, Complex.ofReal_re]
  have h := amgm_psd hm hP
  rw [hdet, htr, Real.mul_rpow ha.le (inv_nonneg.2 hb.le), Real.inv_rpow hb.le] at h
  have hc : 0 < A0.det.re ^ ((m : ℝ)⁻¹) := Real.rpow_pos_of_pos hb _
  calc A.det.re ^ ((m : ℝ)⁻¹) = A0.det.re ^ ((m : ℝ)⁻¹) *
        (A.det.re ^ ((m : ℝ)⁻¹) * (A0.det.re ^ ((m : ℝ)⁻¹))⁻¹) := by
        field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left h hc.le
end ReciprocityTheory.ChartRestriction.G.AR.Up.RgB
