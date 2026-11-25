-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.GE.dpolyOf_Cmul_f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:54:19.981125+00:00
-- url     : https://prove2.me/submissions/cec64b70-8245-40a6-8762-6ccf29010ebd

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofDApply
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_GE_dmonOf_Cmul

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
variable (F : Fin d → PS k 2 d) {ι : Type} [Fintype ι] (u : ι → Fin d → k)
namespace ReciprocityTheory.ChartRestriction.G.TB.GE
theorem _root_.solution (P : MvPolynomial ι k) (r : k) (f : PS k 1 d) :
    DpolyOf F u P (C r * f) = C r * DpolyOf F u P f := by
  unfold DpolyOf
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [dmonOf_Cmul, mul_left_comm]
end ReciprocityTheory.ChartRestriction.G.TB.GE
