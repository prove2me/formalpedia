-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.GE.dpolyOf_eq_sum_of_subset
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:39:19.660157+00:00
-- url     : https://prove2.me/submissions/344a5692-9422-4ec4-864a-dc58d42aa8cb

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofDApply
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick

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
theorem _root_.solution (P : MvPolynomial ι k) (S : Finset (ι →₀ ℕ)) (hS : P.support ⊆ S)
    (f : PS k 1 d) :
    DpolyOf F u P f = ∑ m ∈ S, C (MvPolynomial.coeff m P) * DmonOf F u m f := by
  unfold DpolyOf
  refine Finset.sum_subset hS ?_
  intro m _ hm
  have h0 : MvPolynomial.coeff m P = 0 := by simpa [MvPolynomial.mem_support_iff] using hm
  simp [h0]
end ReciprocityTheory.ChartRestriction.G.TB.GE
