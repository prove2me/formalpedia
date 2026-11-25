-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.GE.dof_C
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:54:20.184293+00:00
-- url     : https://prove2.me/submissions/4b08c627-5f4d-443a-9cd1-3f6fc3e24db0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofDApply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_GE_dofD_apply

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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.GE
variable {k : Type} [CommRing k] {d : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.TB.GE
theorem _root_.solution (F : Fin d → PS k 2 d) (v : Fin d → k) (r : k) : Dof F v (C r) = 0 := by
  have hC : (C r : PS k 1 d) = r • (1 : PS k 1 d) := by
    rw [MvPowerSeries.smul_eq_C_mul, mul_one]
  rw [← dofD_apply, hC, Derivation.map_smul, Derivation.map_one_eq_zero, smul_zero]
end ReciprocityTheory.ChartRestriction.G.TB.GE
