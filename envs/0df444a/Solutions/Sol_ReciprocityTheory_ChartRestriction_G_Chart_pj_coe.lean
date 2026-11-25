-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.pj_coe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:57:36.480227+00:00
-- url     : https://prove2.me/submissions/8db95192-3ea5-4cf1-93c9-52c0efdba140

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CanonB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasisBaseChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ChartSer
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_pj_eq_mk

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.Canon
open scoped CategoryTheory.Obj
variable {R : Type} [CommRing R] {σ τ : Type} [Finite σ] [Finite τ]
namespace ReciprocityTheory.ChartRestriction.G.Chart
theorem _root_.solution (m : ℕ) (q : MvPolynomial σ R) : pj m (q : MvPowerSeries σ R) = Ideal.Quotient.mk _ q :=
  pj_eq_mk.2 fun _ _ => MvPolynomial.coeff_coe _ _
end ReciprocityTheory.ChartRestriction.G.Chart
