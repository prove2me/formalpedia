-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.holoOn_eval_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:05:50.050232+00:00
-- url     : https://prove2.me/submissions/d2a5ac57-8d26-4415-ad44-0b91528c56bd

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedC
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_analyticAt_eval_comp

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
open MvPolynomial ReciprocityTheory.AnForm.M
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable {P J : Ideal (MRing ι)} {e : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution (R : AnLogRes P J e) (x : R.X) (f : MRing ι) :
    R.A.HoloOn (R.U x) (fun y => eval (R.lift x y) (map (Int.castRingHom ℂ) f)) := by
  intro j w hw
  exact analyticAt_eval_comp (F := fun w => R.lift x ((R.A.chart j).symm w))
    (fun p => R.holo x p j w hw) f
end ReciprocityTheory.ChartRestriction.G.Geo
