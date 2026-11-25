-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Semi.LB.lcg_empty_cocycle
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:27:55.028372+00:00
-- url     : https://prove2.me/submissions/6b8f1c00-d79b-4b29-ad4c-52fb1cb44552

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_lcg_empty

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
theorem _root_.solution (a b c : PEmpty.{u+1} → L.ι) :
    res (inf_le_left : wchart L (Y := Y) PEmpty.elim a ⊓ wchart L PEmpty.elim b ⊓
        wchart L PEmpty.elim c ≤ wchart L PEmpty.elim a ⊓ wchart L PEmpty.elim b)
        (lcg L (Y := Y) (K := PEmpty) PEmpty.elim PEmpty.elim a b) *
      res (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
        wchart L (Y := Y) PEmpty.elim a ⊓ wchart L PEmpty.elim b ⊓ wchart L PEmpty.elim c ≤
          wchart L PEmpty.elim b ⊓ wchart L PEmpty.elim c)
        (lcg L (Y := Y) (K := PEmpty) PEmpty.elim PEmpty.elim b c) =
      res (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
        wchart L (Y := Y) PEmpty.elim a ⊓ wchart L PEmpty.elim b ⊓ wchart L PEmpty.elim c ≤
          wchart L PEmpty.elim a ⊓ wchart L PEmpty.elim c)
        (lcg L (Y := Y) (K := PEmpty) PEmpty.elim PEmpty.elim a c) := by
  rw [lcg_empty, lcg_empty, lcg_empty, map_one, map_one, map_one, mul_one]
end ReciprocityTheory.ChartRestriction.G.Semi.LB
