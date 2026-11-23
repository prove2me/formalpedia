-- Prove2me | solution 1 for ReciprocityTheory.AnForm.levi_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:43:18.047122+00:00
-- url     : https://prove2.me/submissions/42e837c4-71eb-46ed-8c6f-85315910f610

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm
open Filter Topology
open scoped ContDiff
noncomputable section
variable {ι κ : Type*} [Fintype ι] [Fintype κ]
namespace ReciprocityTheory.AnForm
theorem _root_.solution (φ : (ι → ℂ) → ℝ) (z : ι → ℂ) : levi φ z 0 = 0 := by
  simp [levi]
end ReciprocityTheory.AnForm
