-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.LogPf.sw_y
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:37:39.650505+00:00
-- url     : https://prove2.me/submissions/3928ae82-2fa6-4eba-b177-d728255e3fb6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogInv
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogClosed
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_czSw
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_X
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
theorem _root_.solution (h : PS k 1 d) :
    ev (n := 2) ![pt k d 1, pt k d 0] (ev (n := 2) ![pt k d 1] h) = ev (n := 2) ![pt k d 0] h := by
  have hY : CZ (![pt k (n := 2) d 1] : Fin 1 → Pt k 2 d) := by
    intro j i
    fin_cases j
    simp [pt]
  rw [ev_ev czSw hY]
  congr 1
  funext j i
  fin_cases j
  first
    | exact ev_X czSw 1 i
    | (simp only [Matrix.cons_val_zero]; exact ev_X czSw 1 i)
    | simp [pt, ev_X czSw]
end ReciprocityTheory.ChartRestriction.G.TB.LogPf
