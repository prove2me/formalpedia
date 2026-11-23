-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.GE.dpolyOf_add_P
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:29:42.232812+00:00
-- url     : https://prove2.me/submissions/cc582d9e-a319-45e5-a4db-35a40397a074

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofDApply
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_GE_dpolyOf_eq_sum_of_subset

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
theorem _root_.solution (P Q : MvPolynomial ι k) (f : PS k 1 d) :
    DpolyOf F u (P + Q) f = DpolyOf F u P f + DpolyOf F u Q f := by
  classical
  rw [dpolyOf_eq_sum_of_subset F u (P + Q) (P.support ∪ Q.support) MvPolynomial.support_add f,
    dpolyOf_eq_sum_of_subset F u P (P.support ∪ Q.support) (fun x hx => Finset.mem_union_left _ hx) f,
    dpolyOf_eq_sum_of_subset F u Q (P.support ∪ Q.support) (fun x hx => Finset.mem_union_right _ hx) f,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_add, map_add, add_mul]
end ReciprocityTheory.ChartRestriction.G.TB.GE
