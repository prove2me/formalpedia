-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_rp__e27165827f88
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:24:18.207003+00:00
-- url     : https://prove2.me/submissions/e47b661a-602c-4911-b8d2-191a5a1d1362

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrData
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_id_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res


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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
variable {S : Scheme.{0}} {E : SplitExt S} {G₁ G₂ : Over S} [GrpObj G₁] [GrpObj G₂]
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.solution {X Z : Scheme.{0}} (a : Z ⟶ X) (z : Z) (U : X.Opens) (V : Z.Opens) (hle : V ≤ a ⁻¹ᵁ U) (hz : z ∈ V)
    (u : Γ(X, U)ˣ) : gm (𝟙 Z) z V (res hle (pullU a U u)) = gm a z U u := (gm_res (𝟙 Z) z hle hz _).trans (gm_id_pull a z U (hle hz) u)
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
