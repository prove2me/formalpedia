-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.ptNorm_le_ptNorm_maxMetric
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:27:09.836719+00:00
-- url     : https://prove2.me/submissions/823709cf-95c6-47c6-a893-c1da2cb849a8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_PenMet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial
variable {o : Type*} [CommRing o] {C : Type*} [NormedField C] {ι : Type*} [Fintype ι]
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution (h : ConeMetric C ι) (σ : o →+* C) (d : ℕ)
    (f : MvPolynomial ι o) {z : ι → C} (hz : z ≠ 0) (hle : ‖z‖ ≤ h.ρ z) :
    ptNorm h σ d f z ≤ ptNorm (maxMetric C ι) σ d f z := by
  unfold ptNorm
  exact div_le_div_of_nonneg_left (norm_nonneg _) (pow_pos ((maxMetric C ι).pos z hz) d)
    (pow_le_pow_left₀ (norm_nonneg _) hle d)
end ReciprocityTheory.ChartRestriction.G.Geo
