-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ObjectsChow_DivCycleGeneric_disjoint_iff_isHorizontal_a353c136abe0
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:45:45.90488+00:00
-- url     : https://prove2.me/submissions/e7538ab6-9c21-47ca-8339-e294e02cb505

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ImportsAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PObjectsDivCycleGeneric

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.ObjectsChow
open GroundTheory.Heights₂.Heights.ObjectsChow.DivCycleGeneric
open MvPolynomial
variable {n : ℕ}
attribute [local instance] genericAlgebra
namespace GroundTheory.Heights₂.Heights.ObjectsChow.DivCycleGeneric
theorem _root_.solution (W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing (ReciprocityTheory.ChartRestriction.G.Geo.PBlk n))) :
    Disjoint (intUnits n : Set (ReciprocityTheory.ChartRestriction.G.Geo.MRing (ReciprocityTheory.ChartRestriction.G.Geo.PBlk n)))
      (W : Set (ReciprocityTheory.ChartRestriction.G.Geo.MRing (ReciprocityTheory.ChartRestriction.G.Geo.PBlk n))) ↔ ReciprocityTheory.ChartRestriction.G.Geo.IsHorizontal W := by
  rw [ReciprocityTheory.ChartRestriction.G.Geo.IsHorizontal, Set.disjoint_left, eq_bot_iff]
  constructor
  · intro h m hm
    rw [Ideal.mem_bot]
    by_contra h0
    exact h ⟨m, mem_nonZeroDivisors_of_ne_zero h0, rfl⟩ hm
  · rintro h _ ⟨m, hm, rfl⟩ hW
    exact nonZeroDivisors.ne_zero hm (Ideal.mem_bot.mp (h hW))
end GroundTheory.Heights₂.Heights.ObjectsChow.DivCycleGeneric
