-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.LogPf.constantCoeff_prim
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:52:28.181868+00:00
-- url     : https://prove2.me/submissions/e8ce8a1c-fff7-4d7d-a120-77d5ffaea8d1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogChain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogPoinc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_coeff_prim

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.LogPf
variable {k : Type} [CommRing k] [Algebra ℚ k] {τ : Type} [Fintype τ] [DecidableEq τ]
namespace ReciprocityTheory.ChartRestriction.G.TB.LogPf
theorem _root_.solution (ω : τ → MvPowerSeries τ k) : constantCoeff (prim ω) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_prim]
  simp
end ReciprocityTheory.ChartRestriction.G.TB.LogPf
