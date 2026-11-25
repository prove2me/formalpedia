-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.gmRP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:05:13.783232+00:00
-- url     : https://prove2.me/submissions/63a1308e-d0ee-45fe-b32d-d3e698bf1a75

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_BaseChangeKernels_PreLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_BaseChangeKernels_UnitsEq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.GtBCPf
open Semi Geo.Tor PullGtPf
namespace ReciprocityTheory.ChartRestriction.G.Out.GtBCPf
theorem _root_.solution {X Z : Scheme.{0}} (a : Z ⟶ X) (z : Z) (U : X.Opens) (V : Z.Opens) (hle : V ≤ a ⁻¹ᵁ U)
    (hz : z ∈ V) (u : Γ(X, U)ˣ) : gm (𝟙 Z) z V (res hle (pullU a U u)) = gm a z U u :=
  (gm_res (𝟙 Z) z hle hz _).trans ((gm_pull (𝟙 Z) a z U (hle hz) u).trans (by rw [Category.id_comp]))
end ReciprocityTheory.ChartRestriction.G.Out.GtBCPf
