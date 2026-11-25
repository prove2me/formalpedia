-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Semi.LB.dg_cocycle
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:27:15.878332+00:00
-- url     : https://prove2.me/submissions/27952c16-dfbb-4329-b36e-a64d45cd6172

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_res_cocycle
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_res_dg

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
theorem _root_.solution {M L : LB X} (hM : M.IsLB) (hL : L.IsLB) (p q r : M.ι × L.ι) :
    res (inf_le_left : M.U p.1 ⊓ L.U p.2 ⊓ (M.U q.1 ⊓ L.U q.2) ⊓ (M.U r.1 ⊓ L.U r.2) ≤
        M.U p.1 ⊓ L.U p.2 ⊓ (M.U q.1 ⊓ L.U q.2)) (dg M L p q) *
      res (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
        M.U p.1 ⊓ L.U p.2 ⊓ (M.U q.1 ⊓ L.U q.2) ⊓ (M.U r.1 ⊓ L.U r.2) ≤
          M.U q.1 ⊓ L.U q.2 ⊓ (M.U r.1 ⊓ L.U r.2)) (dg M L q r) =
      res (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
        M.U p.1 ⊓ L.U p.2 ⊓ (M.U q.1 ⊓ L.U q.2) ⊓ (M.U r.1 ⊓ L.U r.2) ≤
          M.U p.1 ⊓ L.U p.2 ⊓ (M.U r.1 ⊓ L.U r.2)) (dg M L p r) := by
  rw [res_dg, res_dg, res_dg, mul_mul_mul_comm, ← mul_inv]
  exact congrArg₂ (fun a b => a * b⁻¹) (res_cocycle hM _ _ _ _ _ _) (res_cocycle hL _ _ _ _ _ _)
end ReciprocityTheory.ChartRestriction.G.Semi.LB
