-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gaugeBilinearTerm_eq_neg_double_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:56:53.12063+00:00
-- url     : https://prove2.me/submissions/c793aff8-56d1-43d8-8ba2-2f7866cbbce2

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeBilinearTermEqNegDoubleSum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_coeff_ev_zero_right

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
theorem _root_.solution (h : PS k 2 d) (i j : Fin d) :
    sg1 k h i j = -coeff (single ((0 : Fin 2), j) 1 + single ((1 : Fin 2), i) 1) h := by
  show coeff (single ((0 : Fin 1), j) 1) (-ev (n := 1) ![pt k d 0, 0] (pderiv k ((1 : Fin 2), i) h)) = _
  rw [map_neg, coeff_ev_zero_right, Finsupp.embDomain_single, coeff_pderiv]
  have he : eXv d ((0 : Fin 1), j) = ((0 : Fin 2), j) := rfl
  rw [he]
  simp [Finsupp.single_apply]
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
