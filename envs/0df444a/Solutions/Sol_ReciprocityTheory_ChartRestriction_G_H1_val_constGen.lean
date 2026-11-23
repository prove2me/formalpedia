-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.H1.val_constGen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:40:08.853095+00:00
-- url     : https://prove2.me/submissions/4777a208-862d-4ab6-b65a-79e398bb5e1b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_GenMove
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ConstGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ThetaMove
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res


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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.H1
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace ReciprocityTheory.ChartRestriction.G.H1
theorem _root_.solution {S : Scheme.{0}} {A : Over S} [GrpObj A] (L : LB A.left) {T : Over S} (c : Γ(T.left, ⊤)ˣ)
    {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z) (J : (Z ⟶ A.left) → L.ι) :
    val (constGen A L c) r z J = gm (r ≫ (fst T A).left) z ⊤ c := by
  show gm r z _ (res le_top (pullU (fst T A).left ⊤ c)) = _
  exact (gm_res r z _ (Set.mem_iInter.2 fun k => k.elim) _).trans (gm_pull r _ z ⊤ trivial c)
end ReciprocityTheory.ChartRestriction.G.H1
