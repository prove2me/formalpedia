-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_encard_biUnion_finset_le_8a3bd962f7b6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:39:31.422208+00:00
-- url     : https://prove2.me/submissions/462e4d94-5a10-4840-88f1-5ff54816bce4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIsolatedPointsCountPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PIsolatedPointsCount

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
open MvPolynomial Topology ComplexSets
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {ι α : Type*} (S : Finset ι) (f : ι → Set α) :
    (⋃ i ∈ S, f i).encard ≤ ∑ i ∈ S, (f i).encard := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.set_biUnion_insert]
    exact (Set.encard_union_le _ _).trans (add_le_add_right ih _)
end GroundTheory.Heights₂.Heights
