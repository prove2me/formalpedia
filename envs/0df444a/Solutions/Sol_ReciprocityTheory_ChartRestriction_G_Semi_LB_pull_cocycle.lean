-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Semi.LB.pull_cocycle
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:44:58.321221+00:00
-- url     : https://prove2.me/submissions/909d6f92-aae4-4b6b-b642-f7b32eae46e6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_res_pullU_eq

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
namespace ReciprocityTheory.ChartRestriction.G.Semi.LB
theorem _root_.solution {L : LB X} (hL : L.IsLB) (f : Y ⟶ X) (i j k : L.ι) {W : Y.Opens}
    (h₁ : W ≤ f ⁻¹ᵁ (L.U i ⊓ L.U j)) (h₂ : W ≤ f ⁻¹ᵁ (L.U j ⊓ L.U k))
    (h₃ : W ≤ f ⁻¹ᵁ (L.U i ⊓ L.U k)) :
    res h₁ (pullU f _ (L.g i j)) * res h₂ (pullU f _ (L.g j k)) =
      res h₃ (pullU f _ (L.g i k)) := by
  have hW : W ≤ f ⁻¹ᵁ (L.U i ⊓ L.U j ⊓ L.U k) := fun _ hy => ⟨h₁ hy, (h₂ hy).2⟩
  rw [res_pullU_eq f (inf_le_left : L.U i ⊓ L.U j ⊓ L.U k ≤ L.U i ⊓ L.U j) h₁ hW,
    res_pullU_eq f (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
      L.U i ⊓ L.U j ⊓ L.U k ≤ L.U j ⊓ L.U k) h₂ hW,
    res_pullU_eq f (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
      L.U i ⊓ L.U j ⊓ L.U k ≤ L.U i ⊓ L.U k) h₃ hW,
    ← map_mul, ← map_mul, hL.cocycle]
end ReciprocityTheory.ChartRestriction.G.Semi.LB
