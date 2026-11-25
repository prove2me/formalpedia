-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.fourCoeff_eq_fiG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:42:46.96367+00:00
-- url     : https://prove2.me/submissions/506c1f79-db5a-442c-895d-f7b8c1bfcf7a

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FourIndep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology Set
open scoped Interval
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution {f : ℕ} (h : (Fin f → ℂ) → ℂ) (b : Fin f → ℝ) (ν : Fin f → ℤ) :
    fourCoeff h b ν =
      ∫ x in fiBox f, fiG h ν (fun k => (x k : ℂ) + (b k : ℂ) * Complex.I) := rfl
end ReciprocityTheory.L2DbarEstimates.Y
