-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.HasGen.zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:32:00.291718+00:00
-- url     : https://prove2.me/submissions/27dac095-d990-4189-9c97-a5539fed976a

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
theorem _root_.solution : HasGen L (0 : (Y ⟶ X) →₀ ℤ) := by
  refine ⟨Empty, inferInstance, Empty.elim, Empty.elim, ?_, ⟨fun _ => 1⟩, ?_⟩
  · simp [fsum]
  · intro i j
    have hg1 : (LB.LinComb L (Empty.elim : Empty → (Y ⟶ X)) Empty.elim).g i j = 1 :=
      by first
        | (dsimp only [LB.LinComb]; exact Fintype.prod_empty _)
        | (unfold LB.LinComb; exact Fintype.prod_empty _)
        | (simp [LB.LinComb]; rfl)
    dsimp only
    rw [MonoidHom.map_one, MonoidHom.map_one, hg1, one_mul]
end HasGen
end ReciprocityTheory.ChartRestriction.G.DVR
