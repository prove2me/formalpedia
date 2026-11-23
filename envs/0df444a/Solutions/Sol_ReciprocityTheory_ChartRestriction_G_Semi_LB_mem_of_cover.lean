-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Semi.LB.mem_of_cover
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:34:19.883127+00:00
-- url     : https://prove2.me/submissions/2590662b-32ad-48c1-a181-ab77f602e4dc

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
theorem _root_.solution {L : LB X} (hL : L.IsLB) (x : X) : ∃ i, x ∈ L.U i := by
  have hx : x ∈ (⨆ i, L.U i) := by rw [hL.cover]; trivial
  exact TopologicalSpace.Opens.mem_iSup.1 hx
end ReciprocityTheory.ChartRestriction.G.Semi.LB
