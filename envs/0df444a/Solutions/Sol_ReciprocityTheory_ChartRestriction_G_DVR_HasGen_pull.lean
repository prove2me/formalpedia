-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.HasGen.pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:02:40.262526+00:00
-- url     : https://prove2.me/submissions/ce19a9d8-8d3a-435f-8c42-218a9417c018

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullUUnitsCompatGeneric
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_HasGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_fsum_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen_of_isGen


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi
variable {X Y Z : Scheme.{0}} (L : LB X)
variable {L}
namespace ReciprocityTheory.ChartRestriction.G.DVR
namespace HasGen
theorem _root_.solution {F : (Y ⟶ X) →₀ ℤ} (hF : HasGen L F) (h : Z ⟶ Y) :
    HasGen L (Finsupp.mapDomain (fun ψ => h ≫ ψ) F) := by
  obtain ⟨K, _, φ, ε, rfl, g, hg⟩ := hF
  exact ⟨K, inferInstance, fun k => h ≫ φ k, ε, fsum_comp φ ε h, LB.pullGen L φ ε g h,
    pullGen_isGen_of_isGen (L := L) φ ε g hg h⟩
end HasGen
end ReciprocityTheory.ChartRestriction.G.DVR
