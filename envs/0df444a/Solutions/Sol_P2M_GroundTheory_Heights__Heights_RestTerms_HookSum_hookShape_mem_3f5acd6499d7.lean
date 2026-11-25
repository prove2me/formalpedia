-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_HookSum_hookShape_mem_3f5acd6499d7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:52:25.322694+00:00
-- url     : https://prove2.me/submissions/8e5a2877-6e1f-4cca-9f79-00bcfe6adbc6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsTop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PowerSums
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Expand
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PHookCharacterSumIdentity
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_HookSum_sum_hookShape_d3ef97502cd4

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
open GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset
noncomputable section
open GroundTheory.Heights₂.Heights.RestTerms.HookSum
namespace GroundTheory.Heights₂.Heights.RestTerms.HookSum
theorem _root_.solution (r k l : ℕ) (hlr : l < r) (hlk : l < k) :
    hookShape r k l ∈ partitionsOf r k := by
  rw [partitionsOf, Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple]
  refine ⟨by rw [sum_hookShape r k l hlr]; omega, ?_⟩
  intro i j hij
  have := Fin.le_iff_val_le_val.mp hij
  simp only [hookShape]
  split_ifs <;> omega
end GroundTheory.Heights₂.Heights.RestTerms.HookSum
