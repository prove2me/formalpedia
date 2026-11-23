-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.Conv.sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:14:43.740508+00:00
-- url     : https://prove2.me/submissions/3c2abe6d-9df7-4a45-a7f4-c36f02ca6ab7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffRescaleExpandOfNotDvd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModEvalSer
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_Conv_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_CoeffIn_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_IsMF_add


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
namespace ReciprocityTheory.ChartRestriction.L1
namespace Conv
theorem _root_.solution {f g : PowerSeries ℂ} (hf : Conv f) (hg : Conv g) : Conv (f - g) := by
  intro x hx
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) ((hf x hx).add (hg x hx))
  rw [map_sub, ← add_mul]
  exact mul_le_mul_of_nonneg_right (norm_sub_le _ _) (by positivity)
end Conv
end ReciprocityTheory.ChartRestriction.L1
