-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.coeff_swap_sub_low
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:56:51.604739+00:00
-- url     : https://prove2.me/submissions/c2ee813b-a0c2-4569-8df6-10dd626d7767

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeBilinearTermEqNegDoubleSum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_coeff_eq_zero_of_axes
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_embDomain_swE_apply
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_coeff_ev_swap__ca766616f6db

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
theorem _root_.solution (h : PS k 2 d) (h0 : ev (n := 1) ![0, pt k d 0] h = 0)
    (h1 : ev (n := 1) ![pt k d 0, 0] h = 0) (m : Fin 2 × Fin d →₀ ℕ) (hm : m.degree < 2) :
    coeff m (ev (n := 2) ![pt k d 1, pt k d 0] h - h) = 0 := by
  have hdeg : (embDomain (swE d) m).degree = m.degree := by
    show ∑ i ∈ (embDomain (swE d) m).support, (embDomain (swE d) m) i = ∑ i ∈ m.support, m i
    rw [Finsupp.support_embDomain, Finset.sum_map]
    exact Finset.sum_congr rfl (fun x _ => embDomain_swE_apply m x)
  rw [map_sub, coeff_ev_swap', coeff_eq_zero_of_axes h h0 h1 _ (by rw [hdeg]; exact hm),
    coeff_eq_zero_of_axes h h0 h1 m hm, sub_zero]
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
