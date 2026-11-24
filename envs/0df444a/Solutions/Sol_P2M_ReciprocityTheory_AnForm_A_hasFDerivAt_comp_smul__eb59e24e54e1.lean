-- Prove2me | solution 1 for P2M_ReciprocityTheory_AnForm_A_hasFDerivAt_comp_smul__eb59e24e54e1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:57:41.774394+00:00
-- url     : https://prove2.me/submissions/30282b8f-bbbf-4b19-872e-2e729cb75349

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContinuousTmaxShift
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshRegMax

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Metric Filter Topology
open scoped ContDiff Interval
noncomputable section
variable {ι : Type*} [Fintype ι] [Nonempty ι]
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : (ι → ℝ) → F} (c : ℝ) (t : ι → ℝ) (hg : DifferentiableAt ℝ g (c • t)) :
    HasFDerivAt (fun t => g (c • t)) (c • fderiv ℝ g (c • t)) t := by
  have := hg.hasFDerivAt.comp t ((hasFDerivAt_id t).const_smul c)
  exact this.congr_fderiv (ContinuousLinearMap.ext fun v => by simp)
end ReciprocityTheory.AnForm.A
