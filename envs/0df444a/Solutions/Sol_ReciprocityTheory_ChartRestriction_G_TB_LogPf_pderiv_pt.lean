-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.LogPf.pderiv_pt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:58:50.921818+00:00
-- url     : https://prove2.me/submissions/b95a7807-5895-4c9a-b49c-6bc91e39e074

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ConstantCoeffEv
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogInv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_pt_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_pt


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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.LogPf
variable {k : Type} [CommRing k] {d : ℕ}
variable (G : FGLaw k d)
namespace ReciprocityTheory.ChartRestriction.G.TB.LogPf
theorem _root_.solution {n : ℕ} (v : Fin n × Fin d) (j : Fin n) (i : Fin d) :
    pderiv k v (pt k (n := n) d j i) = if (j, i) = v then 1 else 0 := by
  first
  | rw [pt_apply, MvPowerSeries.pderiv_X, Pi.single_apply]
  | (rw [pt_apply, MvPowerSeries.pderiv_X]; simp [Pi.single_apply])
end ReciprocityTheory.ChartRestriction.G.TB.LogPf
