-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.tvec_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:27:38.915933+00:00
-- url     : https://prove2.me/submissions/77671f63-f176-4582-8655-3d6b4639c21a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RankLie
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RankLin
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RankPf

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
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
attribute [local instance] Over.cartesianMonoidalCategory
variable {R : Type} [CommRing R] {Gx : Over (Spec (CommRingCat.of R))} [GrpObj Gx] {n : ℕ}
  {x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin n) m) ⟶ Gx} (hx : IsUnivChart Gx n x)
include hx
namespace ReciprocityTheory.ChartRestriction.G.Chart
theorem _root_.solution {c c' : Fin n → R} (h : tvec (x := x) c = tvec (x := x) c') : c = c' := by
  rw [← tcoord_tvec hx c, ← tcoord_tvec hx c']
  exact tcoord_congr hx h _ _
end ReciprocityTheory.ChartRestriction.G.Chart
