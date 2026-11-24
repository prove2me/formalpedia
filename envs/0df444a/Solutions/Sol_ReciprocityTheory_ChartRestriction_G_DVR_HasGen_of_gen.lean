-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.HasGen.of_gen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:32:28.889257+00:00
-- url     : https://prove2.me/submissions/46767bcd-8db5-4f91-845e-72dd29bc0c53

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullUUnitsCompatGeneric
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_HasGen

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
theorem _root_.solution {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ} (g : LB.Gen (LB.LinComb L φ ε))
    (hg : g.IsGen) : HasGen L (fsum φ ε) := ⟨K, inferInstance, φ, ε, rfl, g, hg⟩
end HasGen
end ReciprocityTheory.ChartRestriction.G.DVR
