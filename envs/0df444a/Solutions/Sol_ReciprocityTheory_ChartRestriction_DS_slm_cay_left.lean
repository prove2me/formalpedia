-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.slm_cay_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:25:45.046735+00:00
-- url     : https://prove2.me/submissions/705bbfdb-698a-4269-a39d-f52afaa03a12

import Definitions.Def_Formalism_RealPlaceAnalysis_Complexify
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CayleyChartDomainIsOpen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Matrix
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {ε : Fin n → Bool}
local notation "JJ" => Formalism.REAL.Jm
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {h : Matrix (Fin n) (Fin n) ℂ} (hd : (h + 1).det ≠ 0)
    (hd2 : (1 - (h - 1) * (h + 1)⁻¹).det ≠ 0) :
    (1 + (h - 1) * (h + 1)⁻¹) * (1 - (h - 1) * (h + 1)⁻¹)⁻¹ = h := by
  have hu : IsUnit (h + 1).det := isUnit_iff_ne_zero.mpr hd
  have hA1 : (h + 1) * (h + 1)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have hc : (h + 1) * (h - 1) = (h - 1) * (h + 1) := by noncomm_ring
  have e : (h + 1) * ((h - 1) * (h + 1)⁻¹) = h - 1 := by
    rw [← Matrix.mul_assoc, hc, Matrix.mul_assoc, hA1, Matrix.mul_one]
  have key : 1 + (h - 1) * (h + 1)⁻¹ = h * (1 - (h - 1) * (h + 1)⁻¹) := by
    calc 1 + (h - 1) * (h + 1)⁻¹ = h - (h + 1) * ((h - 1) * (h + 1)⁻¹) + (h - 1) * (h + 1)⁻¹ := by
          rw [e]; abel
      _ = h * (1 - (h - 1) * (h + 1)⁻¹) := by noncomm_ring
  have hu2 : IsUnit (1 - (h - 1) * (h + 1)⁻¹).det := isUnit_iff_ne_zero.mpr hd2
  rw [key, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu2, Matrix.mul_one]
end ReciprocityTheory.ChartRestriction.DS
