-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.LogPf.sw_F
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:31:32.778258+00:00
-- url     : https://prove2.me/submissions/0c3774bf-68fe-4221-839c-bf49d8e69524

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogInv
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogClosed
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_czSw
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_ev


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
theorem _root_.solution (h : PS k 1 d) : ev (n := 2) ![pt k d 1, pt k d 0] (ev (n := 2) ![G.F] h) = ev (n := 2) ![G.F] h := by
  have hF : CZ (![G.F] : Fin 1 → Pt k 2 d) := by
    intro j i
    fin_cases j
    simpa using G.const i
  rw [ev_ev czSw hF]
  congr 1
  funext j i
  fin_cases j
  simpa using G.comm i
end ReciprocityTheory.ChartRestriction.G.TB.LogPf
