-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.mem_eigLat_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:13:09.697124+00:00
-- url     : https://prove2.me/submissions/4fc1b376-59f1-4ef4-addf-567462352926

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
namespace ReciprocityTheory.ChartRestriction.G.Chart
theorem _root_.solution {O : Type} (act : O → (Gx ⟶ Gx)) [∀ a, IsMonHom (act a)] (χ : O → R) (c : Fin n → R) :
    c ∈ eigLat hx act χ ↔ ∀ a, tmap hx (act a) c = χ a • c := by
  simp only [eigLat, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero]
end ReciprocityTheory.ChartRestriction.G.Chart
