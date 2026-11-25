-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_IsPullHerm_tensor_388239f11d06
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:34:23.700957+00:00
-- url     : https://prove2.me/submissions/2d6df33b-f7b7-494c-a827-200ad693383c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsFurtherTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsMultiHomogFirstCoordinate
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_TableDegreeThreeBase
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_pullDeg_add_22e9381938f4

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
  {K' : Type*} [Fintype K'] {ι' : K' → Type*} [∀ k, Fintype (ι' k)]
omit [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)]
namespace GroundTheory.Heights₂.Heights.Inter
namespace IsPullHerm
theorem _root_.solution {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} {A B : HermLine ι}
    {A' B' : HermLine ι'} (hA : IsPullHerm κ v A A') (hB : IsPullHerm κ v B B') :
    IsPullHerm κ v (A.tensor B) (A'.tensor B') := by
  refine ⟨?_, fun z => ?_⟩
  · show A'.a + B'.a = pullDeg κ (A.a + B.a)
    rw [hA.1, hB.1, pullDeg_add]
  · show A'.h z * B'.h z = A.h _ * B.h _
    rw [hA.2, hB.2]
end IsPullHerm
end GroundTheory.Heights₂.Heights.Inter
