-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Semi.LB.lcg_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:28:05.583166+00:00
-- url     : https://prove2.me/submissions/8cbd8f51-5e07-4e9f-a300-ed35cab40251

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_pull_g_self
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_res_lcg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
noncomputable section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
universe u
open ReciprocityTheory.ChartRestriction.G.Semi.LB
variable {X Y Z : Scheme.{u}}
variable (L : LB X) {K K' : Type u} [Fintype K] [Fintype K']
namespace ReciprocityTheory.ChartRestriction.G.Semi.LB
theorem _root_.solution {L : LB X} (hL : L.IsLB) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (j : K → L.ι) :
    res (le_inf le_rfl le_rfl : wchart L φ j ≤ wchart L φ j ⊓ wchart L φ j) (lcg L φ ε j j) = 1 := by
  rw [res_lcg]
  exact Finset.prod_eq_one fun k _ => by rw [pull_g_self hL (φ k), one_zpow]
end ReciprocityTheory.ChartRestriction.G.Semi.LB
