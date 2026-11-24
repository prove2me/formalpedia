-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ratioField_le_coordField_177461042b61
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:47:40.804786+00:00
-- url     : https://prove2.me/submissions/76b29a31-086d-42d7-abf8-671c00d5559a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitCenter

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G
noncomputable section
variable {ι : Type} {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (x : Cone n (AlgebraicClosure ℚ)) :
    ratioField x ≤ coordField x := by
  refine IntermediateField.adjoin_le_iff.mpr ?_
  rintro _ ⟨p, rfl⟩
  exact div_mem (IntermediateField.subset_adjoin ℚ _ ⟨⟨p.1, p.2.1⟩, rfl⟩)
    (IntermediateField.subset_adjoin ℚ _ ⟨⟨p.1, p.2.2⟩, rfl⟩)
end GroundTheory.Heights₂.Heights
