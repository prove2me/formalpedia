-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Semi.LB.ts_mulGen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:28:25.820721+00:00
-- url     : https://prove2.me/submissions/e8ec9cab-416f-4d7b-91f4-8b21d63d9332

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
theorem _root_.solution (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ)
    (t : Gen (LinComb L φ ε)) (t' : Gen (LinComb L φ' ε')) (j : K ⊕ K' → L.ι) :
    ts (mulGen L φ ε φ' ε' t t') j =
      res (wchart_inl_le L φ φ' j) (ts t (j ∘ Sum.inl)) *
        res (wchart_inr_le L φ φ' j) (ts t' (j ∘ Sum.inr)) := rfl
end ReciprocityTheory.ChartRestriction.G.Semi.LB
