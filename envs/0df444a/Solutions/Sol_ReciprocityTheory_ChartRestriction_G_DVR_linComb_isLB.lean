-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:55:53.205315+00:00
-- url     : https://prove2.me/submissions/34fba8ae-b7a6-43fd-a95e-5bc527626a8c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubeSymmetricSwapFirst
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_linComb_g_self
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_linComb_cocycle
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_linComb_cover

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
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi
variable {X Y : Scheme.{0}} (L : LB X) (hL : L.IsLB) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
include hL
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution : (LB.LinComb L φ ε).IsLB where
  cover := linComb_cover L hL φ ε
  g_self := fun j => linComb_g_self L hL φ ε j
  cocycle := fun i j l => linComb_cocycle L hL φ ε i j l
end ReciprocityTheory.ChartRestriction.G.DVR
