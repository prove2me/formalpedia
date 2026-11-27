-- Prove2me | solution 2 for ReciprocityTheory.ChartRestriction.G.Geo.supNormOn_restrict
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:33:06.150087+00:00
-- url     : https://prove2.me/submissions/23d6d515-af6b-446e-ac7b-1801fb36f408

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
variable {o : Type*} [CommRing o] {C : Type*} [NormedField C] {ι : Type*}
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution (m : ConeMetric C ι) (σ : o →+* C) (I : Ideal (MvPolynomial ι o))
    (d : ℕ) (f : MvPolynomial ι o) :
    supNormOn (m.restrict (conePts σ I) (conePts_ne_zero σ I)) σ d f = supNorm m σ I d f :=
  rfl
end ReciprocityTheory.ChartRestriction.G.Geo
