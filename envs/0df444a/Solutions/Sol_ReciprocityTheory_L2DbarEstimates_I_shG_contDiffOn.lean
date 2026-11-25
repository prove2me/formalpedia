-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.shG_contDiffOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:16:05.850927+00:00
-- url     : https://prove2.me/submissions/f9b13018-5e27-4b48-9f12-a4daaaf1275b

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_MeasurableSetImageOfIsLocalHomeomorph
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_ShellA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_contDiffOn_of_differentiableOn


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open MeasureTheory Metric Filter Topology Set
open scoped ENNReal ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.I
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (g : Fin n → M → ℂ) (hg : ∀ i, Holo n z (g i)) (e : OpenPartialHomeomorph M (V n))
    (he : IsChart n z e) : ContDiffOn ℂ ∞ (shG n g e.symm) e.target := by
  rw [contDiffOn_euclidean]
  intro i
  exact contDiffOn_of_differentiableOn n _ _ e.open_target (hg i e he)
end ReciprocityTheory.L2DbarEstimates.I
