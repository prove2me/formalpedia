-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Semi.LB.lcg_empty
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:34:19.8466+00:00
-- url     : https://prove2.me/submissions/1219a225-9148-4820-86c0-3046d119a3b1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb

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
theorem _root_.solution (i j : PEmpty.{u+1} → L.ι) :
    lcg L (Y := Y) (K := PEmpty) PEmpty.elim PEmpty.elim i j = 1 :=
  Finset.prod_eq_one fun k _ => k.elim
end ReciprocityTheory.ChartRestriction.G.Semi.LB
