-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.CoeffIn.sub1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:28:24.292173+00:00
-- url     : https://prove2.me/submissions/6a920ecd-71fb-4a17-8319-1c3a1e158b1b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffRescaleExpandOfNotDvd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_CoeffIn_xp

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
theorem _root_.solution {R : Subring ℂ} {f : PowerSeries ℂ} (hf : CoeffIn R f) {c : ℂ} (hc : c ∈ R) (k : ℕ) :
    CoeffIn R (sub1 c k f) := by
  have hr : ReciprocityTheory.ChartRestriction.L1.CoeffIn R (PowerSeries.rescale c f) := fun m => by
    rw [PowerSeries.coeff_rescale]
    exact mul_mem (pow_mem hc m) (hf m)
  exact ReciprocityTheory.ChartRestriction.L1.CoeffIn.xp hr k
end CoeffIn
end ReciprocityTheory.ChartRestriction.L1
