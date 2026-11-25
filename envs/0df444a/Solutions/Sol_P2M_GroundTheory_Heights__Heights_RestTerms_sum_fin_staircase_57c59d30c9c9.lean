-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_sum_fin_staircase_57c59d30c9c9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:13:35.47897+00:00
-- url     : https://prove2.me/submissions/dd197aa0-dc84-4002-bb14-0b6f65b1108c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsSchur
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSchNonHookResidues

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open Finset
namespace GroundTheory.Heights₂.Heights.RestTerms
theorem _root_.solution (k : ℕ) : ∑ i : Fin k, (k - 1 - (i : ℕ)) = k * (k - 1) / 2 := by
  have h := Finset.sum_range_reflect (fun i : ℕ => i) k
  rw [Fin.sum_univ_eq_sum_range (fun i => k - 1 - i) k, h, Finset.sum_range_id]
end GroundTheory.Heights₂.Heights.RestTerms
