-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Semi.LB.lcg_cocycle
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:27:48.122797+00:00
-- url     : https://prove2.me/submissions/47dff018-93d1-47a2-a2f7-185052c79f03

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_pull_cocycle
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
theorem _root_.solution {L : LB X} (hL : L.IsLB) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (a b c : K → L.ι) :
    res (inf_le_left : wchart L φ a ⊓ wchart L φ b ⊓ wchart L φ c ≤ wchart L φ a ⊓ wchart L φ b)
        (lcg L φ ε a b) *
      res (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
        wchart L φ a ⊓ wchart L φ b ⊓ wchart L φ c ≤ wchart L φ b ⊓ wchart L φ c)
        (lcg L φ ε b c) =
      res (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
        wchart L φ a ⊓ wchart L φ b ⊓ wchart L φ c ≤ wchart L φ a ⊓ wchart L φ c)
        (lcg L φ ε a c) := by
  rw [res_lcg, res_lcg, res_lcg, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← mul_zpow]
  exact congrArg (· ^ ε k) (pull_cocycle hL (φ k) _ _ _ _ _ _)
end ReciprocityTheory.ChartRestriction.G.Semi.LB
