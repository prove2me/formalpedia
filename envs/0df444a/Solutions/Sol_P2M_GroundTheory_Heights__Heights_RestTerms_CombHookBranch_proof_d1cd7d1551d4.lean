-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_CombHookBranch_proof_d1cd7d1551d4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:42:28.251041+00:00
-- url     : https://prove2.me/submissions/64633d95-cfd6-4bbc-b916-fda52e7b3172

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsComb
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCombHookBranch
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_CombHookBranch_unconditional_f6fa19ac00af

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
open Finset Comb
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace CombHookBranch
theorem _root_.solution (_h1 : CombHookShapeFacts.Statement) : CombHookBranch.Statement :=
  CombHookBranch.unconditional
end CombHookBranch
end GroundTheory.Heights₂.Heights.RestTerms
