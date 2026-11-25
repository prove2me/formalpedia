-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.pa_cs_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:12:27.706017+00:00
-- url     : https://prove2.me/submissions/a5aab582-6fb9-4c36-bd6d-0d7c79c44289

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_CardSupportLeAndSumTwoPowLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_IntegrableNormPowMulExpNegMulNormSq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropAA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Complex
noncomputable section
variable {ι : Type} [Fintype ι]
open Classical
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution {X A B : ℝ} (hX : 0 ≤ X) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : ∀ t : ℝ, 0 < t → 2 * t * X ≤ t ^ 2 * A + B) : X ≤ Real.sqrt A * Real.sqrt B := by
  rw [← Real.sqrt_mul hA]
  rcases hX.lt_or_eq with hX | hX
  · rcases hA.lt_or_eq with hA' | hA'
    · have := h (X / A) (div_pos hX hA')
      have e : (X / A) ^ 2 * A = X * (X / A) := by field_simp
      rw [e] at this
      have h2 : X * X ≤ A * B := by
        have : X * (X / A) ≤ B := by nlinarith
        rw [mul_div_assoc', div_le_iff₀ hA'] at this
        linarith
      exact Real.le_sqrt_of_sq_le (by nlinarith)
    · exfalso
      have := h ((B + 1) / X) (by positivity)
      rw [← hA'] at this
      have e : 2 * ((B + 1) / X) * X = 2 * (B + 1) := by field_simp
      rw [e] at this
      linarith
  · rw [← hX]; exact Real.sqrt_nonneg _
end ReciprocityTheory.ChartRestriction.G.I2
