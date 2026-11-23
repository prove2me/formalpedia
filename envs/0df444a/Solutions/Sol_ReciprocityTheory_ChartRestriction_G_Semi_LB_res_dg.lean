-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Semi.LB.res_dg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:55:15.077525+00:00
-- url     : https://prove2.me/submissions/9dcc1178-40c3-4a2b-82b6-b6a9df94cbc1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_res_res

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
theorem _root_.solution (M L : LB X) (p q : M.ι × L.ι) {W : X.Opens}
    (hW : W ≤ M.U p.1 ⊓ L.U p.2 ⊓ (M.U q.1 ⊓ L.U q.2)) :
    res hW (dg M L p q) =
      res (hW.trans (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)))
        (M.g p.1 q.1) *
      (res (hW.trans (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)))
        (L.g p.2 q.2))⁻¹ := by
  simp only [dg, map_mul, map_inv, res_res]
end ReciprocityTheory.ChartRestriction.G.Semi.LB
