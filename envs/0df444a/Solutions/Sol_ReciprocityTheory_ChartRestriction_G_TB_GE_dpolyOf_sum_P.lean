-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.GE.dpolyOf_sum_P
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:36:10.203647+00:00
-- url     : https://prove2.me/submissions/e87bbee5-3bc0-484e-bc1e-49d85905571b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofDApply
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_GE_dpolyOf_add_P
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_GE_dpolyOf_zero_P

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
theorem _root_.solution {α : Type} (s : Finset α) (P : α → MvPolynomial ι k) (f : PS k 1 d) :
    DpolyOf F u (∑ a ∈ s, P a) f = ∑ a ∈ s, DpolyOf F u (P a) f := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.sum_empty]
    exact dpolyOf_zero_P F u f
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, dpolyOf_add_P, ih]
end ReciprocityTheory.ChartRestriction.G.TB.GE
