-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.continuous_weightFunction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:37:34.048776+00:00
-- url     : https://prove2.me/submissions/ae38c167-9438-41fc-bc47-ee340b33a2c1

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_MeasurableSetImageOfIsLocalHomeomorph
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_LocalExtensionEqMulJacobian
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_smooth
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_continuous


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff
namespace ReciprocityTheory.L2DbarEstimates.I
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (hz : IsLocalHomeomorph z) (g : Fin n → M → ℂ) (ph : M → ℝ) (r : ℝ)
    (hg : ∀ i, Holo n z (g i)) (hph : SmoothR n z ph) : Continuous (ev n g ph r) := by
  have hgc : ∀ i, Continuous (g i) := fun i => Smooth.continuous n z hz _ (Holo.smooth n z _ (hg i))
  have hpc : Continuous ph := by
    have := Smooth.continuous n z hz _ hph
    exact Complex.continuous_re.comp this |>.congr (fun x => by simp)
  unfold ev
  fun_prop
end ReciprocityTheory.L2DbarEstimates.I
