-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.coeff_xp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:17:39.198576+00:00
-- url     : https://prove2.me/submissions/5c5f854e-7215-4d1b-aba2-39a8752eaf95

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
theorem _root_.solution {R : Type*} [CommRing R] (k : ℕ) (f : PowerSeries R) (n : ℕ) :
    PowerSeries.coeff n (xp k f) = if k ∣ n then PowerSeries.coeff (n / k) f else 0 := by
  rw [xp, PowerSeries.coeff_mk]
end ReciprocityTheory.ChartRestriction.L1
