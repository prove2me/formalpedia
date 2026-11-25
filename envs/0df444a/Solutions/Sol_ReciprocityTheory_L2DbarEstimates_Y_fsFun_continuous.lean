-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.fsFun_continuous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:06:07.627013+00:00
-- url     : https://prove2.me/submissions/c784713b-92f0-4cbb-bfd9-d649870539a6

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FourSum
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fsFun_proj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal Pointwise Matrix
noncomputable section
universe u
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution {f : ℕ} (g : (Fin f → ℝ) → ℂ) (hg : Continuous g)
    (hper : ∀ x (n : Fin f → ℤ), g (x + fun i => (n i : ℝ)) = g x) :
    Continuous (fsFun g) := by
  rw [(fsProj_isOpenQuotientMap f).isQuotientMap.continuous_iff]
  have : fsFun g ∘ fsProj f = g := funext fun t => fsFun_proj g hper t
  rw [this]; exact hg
end ReciprocityTheory.L2DbarEstimates.Y
