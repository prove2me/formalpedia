-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.pa_bound2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:28:31.807916+00:00
-- url     : https://prove2.me/submissions/5d27affa-a6e9-4f3e-855a-0b5af3030425

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_CardSupportLeAndSumTwoPowLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_IntegrableNormPowMulExpNegMulNormSq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropAA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_paPoly_growth
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_paW_pos

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
theorem _root_.solution {q c : ℕ} (hq : 1 ≤ q) {F G : EuclideanSpace ℂ ι → ℂ} (hF : F ∈ paPoly c)
    (hG : G ∈ paPoly c) : ∃ C : ℝ, 0 ≤ C ∧ ∀ v, ‖F v‖ * ‖G v‖ * paW q v ≤
      C * ((1 + ‖v‖) ^ (2 * c) * Real.exp (-(q * Real.pi) * ‖v‖ ^ 2)) := by
  obtain ⟨C1, h1, hC1⟩ := paPoly_growth hF
  obtain ⟨C2, h2, hC2⟩ := paPoly_growth hG
  refine ⟨C1 * C2, by positivity, fun v => ?_⟩
  have hw := (paW_pos q v).le
  have e : (1 + ‖v‖) ^ (2 * c) = (1 + ‖v‖) ^ c * (1 + ‖v‖) ^ c := by rw [two_mul, pow_add]
  rw [e, paW]
  have := mul_le_mul (hC1 v) (hC2 v) (norm_nonneg _) (by positivity)
  have hw' := Real.exp_pos (-(q * Real.pi) * ‖v‖ ^ 2)
  nlinarith
end ReciprocityTheory.ChartRestriction.G.I2
