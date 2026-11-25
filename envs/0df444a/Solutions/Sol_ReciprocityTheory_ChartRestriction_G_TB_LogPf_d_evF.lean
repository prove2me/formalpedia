-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.LogPf.d_evF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:53:59.564461+00:00
-- url     : https://prove2.me/submissions/4ddc2d32-7313-4d36-804e-5f1afc8d1816

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogInv
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogClosed
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_pderiv_ev


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
theorem _root_.solution (h : PS k 1 d) (v : Fin 2 × Fin d) :
    pderiv k v (ev (n := 2) ![G.F] h) = ∑ c, ev (n := 2) ![G.F] (pderiv k ((0 : Fin 1), c) h) * pderiv k v (G.F c) := by
  have hF : CZ (![G.F] : Fin 1 → Pt k 2 d) := by
    intro j i
    fin_cases j
    simpa using G.const i
  rw [pderiv_ev hF, Fintype.sum_prod_type]
  simp
end ReciprocityTheory.ChartRestriction.G.TB.LogPf
