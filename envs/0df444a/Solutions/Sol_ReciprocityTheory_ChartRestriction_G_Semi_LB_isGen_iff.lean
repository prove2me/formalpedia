-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Semi.LB.isGen_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:32:02.105343+00:00
-- url     : https://prove2.me/submissions/7a0efbf4-92a6-4430-9d21-6a04fbc1f116

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
theorem _root_.solution {φ : K → (Y ⟶ X)} {ε : K → ℤ} (t : Gen (LinComb L φ ε)) :
    t.IsGen ↔ ∀ i j : K → L.ι,
      res (inf_le_left : wchart L φ i ⊓ wchart L φ j ≤ wchart L φ i) (ts t i) =
        lcg L φ ε i j * res (inf_le_right : wchart L φ i ⊓ wchart L φ j ≤ wchart L φ j) (ts t j) :=
  Iff.rfl
end ReciprocityTheory.ChartRestriction.G.Semi.LB
