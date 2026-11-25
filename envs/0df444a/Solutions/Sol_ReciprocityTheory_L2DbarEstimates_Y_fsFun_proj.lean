-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.fsFun_proj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:52:01.538839+00:00
-- url     : https://prove2.me/submissions/14907713-46ac-4747-8fcd-04bd2d560e60

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FourSum
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fsProj_eq

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
theorem _root_.solution {f : ℕ} (g : (Fin f → ℝ) → ℂ)
    (hper : ∀ x (n : Fin f → ℤ), g (x + fun i => (n i : ℝ)) = g x) (t : Fin f → ℝ) :
    fsFun g (fsProj f t) = g t := by
  unfold fsFun
  set s := Function.surjInv (fsProj_isOpenQuotientMap f).surjective (fsProj f t)
  have hs : fsProj f s = fsProj f t := Function.surjInv_eq _ _
  obtain ⟨n, hn⟩ := fsProj_eq s t hs
  rw [hn, hper]
end ReciprocityTheory.L2DbarEstimates.Y
