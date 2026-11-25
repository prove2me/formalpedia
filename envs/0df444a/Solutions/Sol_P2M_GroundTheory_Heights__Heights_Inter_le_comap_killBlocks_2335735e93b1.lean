-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_le_comap_killBlocks_2335735e93b1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:19:13.67401+00:00
-- url     : https://prove2.me/submissions/ec7032f8-7dda-41f1-9165-b19b2853838e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_RationalSections_ThmISt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_UniquenessDegreeFormOfIntersectionForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ArithVarZero
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_killBlocks_of_isMultiHomog_a53d8df3215d

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter
theorem _root_.solution {P : Ideal (MRing ι)} (hP : IsMultiHomogIdeal P) (S : Set K) :
    P ≤ P.comap (killBlocks S) := by
  obtain ⟨T, hT, rfl⟩ := hP
  refine Ideal.span_le.mpr fun f hf => ?_
  obtain ⟨a, ha⟩ := hT f hf
  rw [SetLike.mem_coe, Ideal.mem_comap]
  rcases killBlocks_of_isMultiHomog S ha with h | h <;> rw [h]
  · exact Ideal.subset_span hf
  · exact Ideal.zero_mem _
end GroundTheory.Heights₂.Heights.Inter
