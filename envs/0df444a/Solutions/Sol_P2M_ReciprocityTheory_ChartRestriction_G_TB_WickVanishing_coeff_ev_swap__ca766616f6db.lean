-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_coeff_ev_swap__ca766616f6db
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:47:04.675869+00:00
-- url     : https://prove2.me/submissions/af32f276-3b0c-477d-b995-0e9f0b3089ff

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeBilinearTermEqNegDoubleSum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_coeff_ev_swap
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_swE_swE
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_embDomain_swE_apply

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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Finsupp
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
variable {k : Type} [CommRing k] {d : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
theorem _root_.solution (h : PS k 2 d) (m : Fin 2 × Fin d →₀ ℕ) :
    coeff m (ev (n := 2) ![pt k d 1, pt k d 0] h) = coeff (embDomain (swE d) m) h := by
  have hm : embDomain (swE d) (embDomain (swE d) m) = m := by
    ext t
    conv_lhs => rw [← swE_swE t]
    rw [embDomain_swE_apply, embDomain_swE_apply]
  have := coeff_ev_swap h (embDomain (swE d) m)
  rw [hm] at this
  exact this
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
