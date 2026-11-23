-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.CoeffIn.xp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:25:11.539468+00:00
-- url     : https://prove2.me/submissions/233842c4-2043-4566-940a-b160a423d4e3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffRescaleExpandOfNotDvd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_coeff_xp

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
namespace CoeffIn
theorem _root_.solution {R : Subring ℂ} {f : PowerSeries ℂ} (hf : CoeffIn R f) (k : ℕ) : CoeffIn R (xp k f) := by
  intro n
  rw [coeff_xp]
  split_ifs
  · exact hf _
  · exact zero_mem R
end CoeffIn
end ReciprocityTheory.ChartRestriction.L1
