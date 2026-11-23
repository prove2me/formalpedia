-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.CoeffIn.add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:33:13.472886+00:00
-- url     : https://prove2.me/submissions/eff3fa62-71bf-413d-aa6d-1a9efb1f3424

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffRescaleExpandOfNotDvd

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
theorem _root_.solution {R : Subring ℂ} {f g : PowerSeries ℂ} (hf : CoeffIn R f) (hg : CoeffIn R g) :
    CoeffIn R (f + g) := by
  intro n
  rw [map_add]
  exact add_mem (hf n) (hg n)
end CoeffIn
end ReciprocityTheory.ChartRestriction.L1
