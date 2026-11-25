-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.tvec_eig_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:54:06.735091+00:00
-- url     : https://prove2.me/submissions/55d4d2c6-854e-421e-b8dc-0891505edeba

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RankLie
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RankLin
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RankPf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tvec_inj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tvec_tmap


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
namespace ReciprocityTheory.ChartRestriction.G.Chart
theorem _root_.solution (e : Gx ⟶ Gx) [IsMonHom e] (c : Fin n → R) (s : R) :
    tvec (x := x) c ≫ e = spMap (scaleD s) ≫ tvec (x := x) c ↔ tmap hx e c = s • c := by
  rw [← tvec_tmap hx, ← tvec_smul hx]
  exact ⟨fun h => tvec_inj hx h, fun h => by rw [h]⟩
end ReciprocityTheory.ChartRestriction.G.Chart
