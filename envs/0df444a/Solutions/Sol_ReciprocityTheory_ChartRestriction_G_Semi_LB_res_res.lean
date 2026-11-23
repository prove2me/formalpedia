-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Semi.LB.res_res
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:30:31.236327+00:00
-- url     : https://prove2.me/submissions/c0008392-24bd-48a5-983b-c8b39517632f

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
namespace ReciprocityTheory.ChartRestriction.G.Semi.LB
theorem _root_.solution {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (x : Γ(X, U)ˣ) :
    res h₂ (res h₁ x) = res (h₂.trans h₁) x := by
  ext
  change ((X.presheaf.map (homOfLE h₁).op ≫ X.presheaf.map (homOfLE h₂).op).hom) (x : Γ(X, U)) = _
  rw [← Functor.map_comp]
  rfl
end ReciprocityTheory.ChartRestriction.G.Semi.LB
