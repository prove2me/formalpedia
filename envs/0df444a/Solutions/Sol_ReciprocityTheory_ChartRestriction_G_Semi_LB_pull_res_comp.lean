-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Semi.LB.pull_res_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:49:22.804495+00:00
-- url     : https://prove2.me/submissions/0a515abe-a10e-4975-8bed-4cc0fa567699

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_res_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_pullU_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_pullU_comp

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
theorem _root_.solution (h : Z ⟶ Y) (f : Y ⟶ X) (U : X.Opens) {V : Y.Opens} (hV : V ≤ f ⁻¹ᵁ U)
    {W : Z.Opens} (hW : W ≤ h ⁻¹ᵁ V) (hW' : W ≤ (h ≫ f) ⁻¹ᵁ U) (x : Γ(X, U)ˣ) :
    res hW (pullU h V (res hV (pullU f U x))) = res hW' (pullU (h ≫ f) U x) := by
  rw [pullU_res, res_res, pullU_comp]
  rfl
end ReciprocityTheory.ChartRestriction.G.Semi.LB
