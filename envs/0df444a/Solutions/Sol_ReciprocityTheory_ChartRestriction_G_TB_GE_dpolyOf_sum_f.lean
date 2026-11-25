-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.GE.dpolyOf_sum_f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:15:34.350818+00:00
-- url     : https://prove2.me/submissions/ed392628-412e-4b4e-ba49-efbfa47ab40c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofDApply
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_GE_dmonOf_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_GE_dpolyOf_add_f

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
theorem _root_.solution {α : Type} (s : Finset α) (P : MvPolynomial ι k) (f : α → PS k 1 d) :
    DpolyOf F u P (∑ a ∈ s, f a) = ∑ a ∈ s, DpolyOf F u P (f a) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.sum_empty]
    unfold DpolyOf
    simp [dmonOf_zero]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, dpolyOf_add_f, ih]
end ReciprocityTheory.ChartRestriction.G.TB.GE
