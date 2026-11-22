-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.val_cub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:39:58.495083+00:00
-- url     : https://prove2.me/submissions/8e82fc77-80cc-4e5d-af20-4ed318bd8681

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : RigLB G} (c : CubicalStr G L)
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.solution {T T' : Over S} (ρ : T' ⟶ T) {z : T'.left} {J : (T'.left ⟶ G.left) → L.L.ι} (hJ : Good L.L z J)
    (x x' y : T ⟶ G) : val (LB.pullGen L.L (thφ G (x3 G)) thε c.t (lift x (lift x' y)).left) ρ.left z J =
      cubV c z J (ρ ≫ x) (ρ ≫ x') (ρ ≫ y) := by
  refine (val_pull hJ _ _ _).trans ?_
  rw [← Over.comp_left, comp_lift, comp_lift]; rfl
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
