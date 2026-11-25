-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.LogPf.om_P
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:08:10.8228+00:00
-- url     : https://prove2.me/submissions/4b73f083-2c15-4159-93ba-cebe6facf043

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogInv
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogClosed
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_om_Q
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_czSw
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_sw_F
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_sw_y
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_sw_dF
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_C
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_mul


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
theorem _root_.solution (i a : Fin d) :
    ∑ j, ev (n := 2) ![G.F] (Om G i j) * pderiv k ((0 : Fin 2), a) (G.F j) = ev (n := 2) ![pt k d 0] (Om G i a) := by
  have h := congrArg (ev (n := 2) ![pt k d 1, pt k d 0]) (om_Q G i a)
  let f : PS k 2 d →+* PS k 2 d :=
    { toFun := ev (n := 2) ![pt k d 1, pt k d 0]
      map_one' := by simpa using ev_C czSw (1 : k)
      map_mul' := ev_mul czSw
      map_zero' := by simpa using ev_C czSw (0 : k)
      map_add' := ev_add czSw }
  have hs : ∀ (s : Finset (Fin d)) (g : Fin d → PS k 2 d),
      ev (n := 2) ![pt k d 1, pt k d 0] (∑ j ∈ s, g j) = ∑ j ∈ s, ev (n := 2) ![pt k d 1, pt k d 0] (g j) :=
    fun s g => map_sum f g s
  rw [hs, sw_y] at h
  simp only [ev_mul czSw, sw_F, Ar, sw_dF] at h
  exact h
end ReciprocityTheory.ChartRestriction.G.TB.LogPf
