-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.HomUniqPf.cz_pt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:02:10.765445+00:00
-- url     : https://prove2.me/submissions/2975221d-acc5-40d7-b532-34d5edd3fda8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_PderivSecondEvFirstPointEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcAdd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ConstantCoeffEv
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_HomUniq
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB
open ReciprocityTheory.ChartRestriction.G.TB.HomUniqPf
open ReciprocityTheory.ChartRestriction.G.TB.LogPf Formalism.FG.SolveVAux
variable {k : Type} [CommRing k] {d : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.TB.HomUniqPf
theorem _root_.solution {n : ℕ} (j : Fin n) : ∀ i, constantCoeff (pt k (n := n) d j i) = 0 := fun i => by
  unfold pt
  exact MvPowerSeries.constantCoeff_X _
end ReciprocityTheory.ChartRestriction.G.TB.HomUniqPf
