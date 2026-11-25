-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_CombExtendWord_proof_65aaa773a61f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:55:24.600961+00:00
-- url     : https://prove2.me/submissions/7c4be314-27f4-4460-9d4f-a5d36c007840

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsComb
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCombExtendWord
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_CombExtendWord_exists_word_1ac480885857

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
noncomputable section
open scoped Classical
open GroundTheory.Heights₂.Heights.RestTerms.CombExtendWord
namespace GroundTheory.Heights₂.Heights.RestTerms.CombExtendWord
theorem _root_.solution (h1 : CombPcntAppend.Statement) : CombExtendWord.Statement := by
  intro m n q μ lam hμ hlam hle hsum
  obtain ⟨s, hs⟩ := exists_word h1 μ hμ q lam hlam hle hsum
  exact ⟨s, hs n⟩
end GroundTheory.Heights₂.Heights.RestTerms.CombExtendWord
