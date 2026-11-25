-- Prove2me | solution 1 for PositivityTheory.CW.EigenGainPolynomial.phi_lb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:24:45.498856+00:00
-- url     : https://prove2.me/submissions/77bc0ecf-1e27-4ef7-ba60-863662e7ce3d

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_BasisFormSumOfGain

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS
open PositivityTheory PositivityTheory.CW
open PositivityTheory.CW.EigenGainPolynomial
namespace PositivityTheory.CW.EigenGainPolynomial
theorem _root_.solution (s : ℕ) (c ν x : ℝ) (hν : 0 ≤ ν) (hx : 0 ≤ x)
    (hA : ∀ y : ℝ, -1 < y → 1 - s * y + (s : ℝ) ^ 2 / 4 * y ^ 2 - c * y ^ 4 ≤ ((1 + y) ^ s)⁻¹) :
    ((1 + ν) ^ s)⁻¹ + (-(((1 + ν) ^ s)⁻¹ * s / (1 + ν))) * (x - ν)
      + (((1 + ν) ^ s)⁻¹ * (s : ℝ) ^ 2 / (4 * (1 + ν) ^ 2)) * ((x - ν) * (x - ν))
      + (-(((1 + ν) ^ s)⁻¹ * c / (1 + ν) ^ 4)) * ((x - ν) * (x - ν) * ((x - ν) * (x - ν)))
      ≤ ((1 + x) ^ s)⁻¹ := by
  have h1 : (0 : ℝ) < 1 + ν := by linarith
  have hy1 : -1 < (x - ν) / (1 + ν) := by
    rw [lt_div_iff₀ h1]; linarith
  have hA' := hA _ hy1
  have hx1 : 1 + x = (1 + ν) * (1 + (x - ν) / (1 + ν)) := by field_simp; ring
  have ha : 0 ≤ ((1 + ν) ^ s)⁻¹ := by positivity
  calc _ = ((1 + ν) ^ s)⁻¹ * (1 - s * ((x - ν) / (1 + ν)) + (s : ℝ) ^ 2 / 4 * ((x - ν) / (1 + ν)) ^ 2
          - c * ((x - ν) / (1 + ν)) ^ 4) := by
          field_simp; ring
    _ ≤ ((1 + ν) ^ s)⁻¹ * ((1 + (x - ν) / (1 + ν)) ^ s)⁻¹ := mul_le_mul_of_nonneg_left hA' ha
    _ = ((1 + x) ^ s)⁻¹ := by rw [hx1, mul_pow, mul_inv]
end PositivityTheory.CW.EigenGainPolynomial
