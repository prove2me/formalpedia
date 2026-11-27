-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.ptNorm_eq_ptNorm_maxMetric
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:27:04.370882+00:00
-- url     : https://prove2.me/submissions/8395095d-3e17-43b4-8210-f3a9cae252c2

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
    (f : MvPolynomial ι o) {z : ι → C} (heq : ‖z‖ = h.ρ z) :
    ptNorm h σ d f z = ptNorm (maxMetric C ι) σ d f z := by
  unfold ptNorm
  rw [← heq]
  rfl
end ReciprocityTheory.ChartRestriction.G.Geo
