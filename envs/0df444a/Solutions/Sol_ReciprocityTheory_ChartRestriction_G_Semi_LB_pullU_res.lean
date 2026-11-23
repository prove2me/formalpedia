-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Semi.LB.pullU_res
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:32:21.241458+00:00
-- url     : https://prove2.me/submissions/c1e4be7f-e612-4d73-a9ee-db6fcc1130e5

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
theorem _root_.solution (f : Y ⟶ X) {U V : X.Opens} (h : V ≤ U) (x : Γ(X, U)ˣ) :
    pullU f V (res h x) = res (f.preimage_mono h) (pullU f U x) := by
  ext
  change ((X.presheaf.map (homOfLE h).op ≫ f.app V).hom) (x : Γ(X, U)) = _
  rw [Scheme.Hom.naturality]
  rfl
end ReciprocityTheory.ChartRestriction.G.Semi.LB
