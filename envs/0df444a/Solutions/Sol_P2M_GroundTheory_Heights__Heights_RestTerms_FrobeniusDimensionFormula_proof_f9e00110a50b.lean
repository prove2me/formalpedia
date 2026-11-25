-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_FrobeniusDimensionFormula_proof_f9e00110a50b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:57:18.2458+00:00
-- url     : https://prove2.me/submissions/cc85da17-bef0-41dc-ac21-ea99051796e2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsComb
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PFrobeniusDimensionFormula

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
open Comb
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace FrobeniusDimensionFormula
theorem _root_.solution (h1 : CombTableEqWords.Statement)
    (h2 : CombCfAtStair.Statement) (h3 : CombCfVandermondePsumOne.Statement) :
    FrobeniusDimensionFormula.Statement := by
  intro m lam hlam
  have hsum : ∑ i, (lam i + stair m i) = ∑ i, stair m i + ∑ i, lam i := by
    rw [Finset.sum_add_distrib, add_comm]
  have e := h3 m (∑ i, lam i) (fun i => lam i + stair m i) hsum
  rw [h2 m (∑ i, lam i) lam hlam] at e
  rw [h1 m lam hlam, e]
  simp only [stair]
end FrobeniusDimensionFormula
end GroundTheory.Heights₂.Heights.RestTerms
