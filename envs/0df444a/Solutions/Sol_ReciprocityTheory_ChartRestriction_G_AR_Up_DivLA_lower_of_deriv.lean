-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.DivLA.lower_of_deriv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:39:07.4535+00:00
-- url     : https://prove2.me/submissions/945c8eff-ffaf-4b8f-9fc1-3580ff082630

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_DivStatementPfLA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_DivStatementPfLB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.DivLA
open ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter Asymptotics
noncomputable section
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.DivLA
theorem _root_.solution {φ : V n → V n} (L : V n ≃L[ℂ] V n)
    (h : (fun z => φ z - L z) =o[𝓝 0] fun z => z) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ z in 𝓝 0, c * ‖z‖ ≤ ‖φ z‖ := by
  set K : ℝ := ‖(L.symm : V n →L[ℂ] V n)‖ + 1 with hK
  have hKpos : 0 < K := by positivity
  refine ⟨1 / (2 * K), by positivity, ?_⟩
  filter_upwards [h.def (show (0 : ℝ) < 1 / (2 * K) by positivity)] with z hz
  have h1 : ‖z‖ ≤ K * ‖L z‖ := by
    calc ‖z‖ = ‖(L.symm : V n →L[ℂ] V n) (L z)‖ := by simp
      _ ≤ ‖(L.symm : V n →L[ℂ] V n)‖ * ‖L z‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ K * ‖L z‖ := by gcongr; linarith
  have h2 : ‖L z‖ ≤ ‖φ z‖ + ‖φ z - L z‖ := by
    calc ‖L z‖ = ‖φ z - (φ z - L z)‖ := by congr 1; abel
      _ ≤ ‖φ z‖ + ‖φ z - L z‖ := norm_sub_le _ _
  have h3 : ‖z‖ / K ≤ ‖L z‖ := by rw [div_le_iff₀ hKpos]; linarith
  have h4 : ‖z‖ / K = 2 * (1 / (2 * K) * ‖z‖) := by field_simp; try ring
  linarith
end ReciprocityTheory.ChartRestriction.G.AR.Up.DivLA
