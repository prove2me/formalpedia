-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_RankAdjoinFrac_proof_1c66895deddb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:01:24.454647+00:00
-- url     : https://prove2.me/submissions/933017bf-37fc-4110-b804-058d8e63bf2a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StRankAdjoinFrac
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRankAdjoinFrac
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_RankAdjoinFrac_finrank_algebraAdjoin_eq_finrank_adjoin_78e55535a125
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_RankAdjoinFrac_finrank_eq_finrank_algebraAdjoin_f7378cb62581

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
open Module IntermediateField IntermediateField.algebraAdjoinAdjoin
open GroundTheory.Heights₂.Heights.Inter.RankAdjoinFrac
namespace GroundTheory.Heights₂.Heights.Inter.RankAdjoinFrac
theorem _root_.solution : RankAdjoinFrac.Statement := by
  intro F Ω _ _ _ S T h
  have hKL : IntermediateField.adjoin F S ≤ IntermediateField.adjoin F T := adjoin.mono F S T h
  have hE : extendScalars hKL = IntermediateField.adjoin (IntermediateField.adjoin F S) T :=
    restrictScalars_injective F (by
      rw [extendScalars_restrictScalars, adjoin_adjoin_left, Set.union_eq_self_of_subset_left h])
  have key : IntermediateField.relfinrank (IntermediateField.adjoin F S) (IntermediateField.adjoin F T) =
      finrank (IntermediateField.adjoin F S) (Algebra.adjoin (IntermediateField.adjoin F S) T) := by
    rw [relfinrank_eq_finrank_of_le hKL, hE, finrank_algebraAdjoin_eq_finrank_adjoin]
  exact (finrank_eq_finrank_algebraAdjoin h).trans key.symm
end GroundTheory.Heights₂.Heights.Inter.RankAdjoinFrac
