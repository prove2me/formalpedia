-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.GE.degLt_secondOrder
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:39:20.05716+00:00
-- url     : https://prove2.me/submissions/484ad690-2a5a-4fe6-a727-d48c9944d0df

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofDApply
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_GE_degLt_mono
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_GE_degLt_pderiv

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
variable {ι : Type} [Fintype ι]
namespace ReciprocityTheory.ChartRestriction.G.TB.GE
theorem _root_.solution (c : ι → ι → k) {n : ℕ} {P : MvPolynomial ι k} (h : DegLt (n + 1) P) :
    DegLt n (secondOrder k c P) := by
  intro m hm
  unfold secondOrder
  rw [MvPolynomial.coeff_sum]
  refine Finset.sum_eq_zero fun l _ => ?_
  rw [MvPolynomial.coeff_sum]
  refine Finset.sum_eq_zero fun l' _ => ?_
  rw [MvPolynomial.coeff_C_mul,
    degLt_pderiv (degLt_mono (Nat.le_succ n) (degLt_pderiv h l')) l m hm, mul_zero]
end ReciprocityTheory.ChartRestriction.G.TB.GE
