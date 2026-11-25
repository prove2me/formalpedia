-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HExp.hasStrict_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:18:37.781471+00:00
-- url     : https://prove2.me/submissions/c237b3c6-554f-4fd0-bd2b-50c5379d1664

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_HaarVolumes_HaarExpA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_HaarVolumes_HaarExpB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HExp_hasStrict_logA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HExp_hasStrict_exp_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HExp
open Filter Topology Metric NormedSpace Asymptotics
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
namespace ReciprocityTheory.ChartRestriction.DS.HExp
theorem _root_.solution (L M : 𝔸 × 𝔸 →L[ℝ] 𝔸) :
    HasStrictFDerivAt (fun p : 𝔸 × 𝔸 => logA 𝔸 (exp (L p) * exp (M p))) (L + M) (0 : 𝔸 × 𝔸) := by
  have h := (hasStrict_exp_comp L).mul' (hasStrict_exp_comp M)
  have hv : ((fun p : 𝔸 × 𝔸 => exp (L p)) * fun p : 𝔸 × 𝔸 => exp (M p)) 0 = 1 := by
    simp [exp_zero]
  have h1 : HasStrictFDerivAt (logA 𝔸) (ContinuousLinearMap.id ℝ 𝔸)
      (((fun p : 𝔸 × 𝔸 => exp (L p)) * fun p : 𝔸 × 𝔸 => exp (M p)) 0) := by
    rw [hv]; exact hasStrict_logA
  refine (h1.comp (0 : 𝔸 × 𝔸) h).congr_fderiv ?_
  ext p <;> simp [exp_zero, add_comm]
end ReciprocityTheory.ChartRestriction.DS.HExp
