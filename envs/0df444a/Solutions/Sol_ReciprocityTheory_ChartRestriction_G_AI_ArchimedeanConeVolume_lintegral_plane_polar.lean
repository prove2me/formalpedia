-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.ArchimedeanConeVolume.lintegral_plane_polar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:27:11.371345+00:00
-- url     : https://prove2.me/submissions/a39a39b0-a220-4d91-a9de-9f27d739cc77

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_KappaA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LintegralIoiOfRealMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Real
open scoped ENNReal Pointwise
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.ArchimedeanConeVolume
namespace ReciprocityTheory.ChartRestriction.G.AI.ArchimedeanConeVolume
theorem _root_.solution (K : ℝ × ℝ → ℝ≥0∞) :
    ∫⁻ p : ℝ × ℝ, K p =
      ∫⁻ q in Ioi (0 : ℝ) ×ˢ Ioo (-π) π, ENNReal.ofReal q.1 * K (q.1 * cos q.2, q.1 * sin q.2) := by
  rw [← lintegral_comp_polarCoord_symm]
  rfl
end ReciprocityTheory.ChartRestriction.G.AI.ArchimedeanConeVolume
