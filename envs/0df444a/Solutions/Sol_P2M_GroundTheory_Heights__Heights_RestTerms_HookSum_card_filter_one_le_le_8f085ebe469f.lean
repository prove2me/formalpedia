-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_HookSum_card_filter_one_le_le_8f085ebe469f
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:04:34.995978+00:00
-- url     : https://prove2.me/submissions/473d95ee-9503-49d6-9dcc-1aee721ca317

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsTop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PowerSums
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Expand
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PHookCharacterSumIdentity

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
theorem _root_.solution (r m : ℕ) (hm : m < r) :
    (Finset.univ.filter fun j : Fin r => 1 ≤ (j : ℕ) ∧ (j : ℕ) ≤ m).card = m := by
  have h : (Finset.univ.filter fun j : Fin r => 1 ≤ (j : ℕ) ∧ (j : ℕ) ≤ m) =
      (Finset.Icc 1 m).attachFin (fun x hx => by rw [Finset.mem_Icc] at hx; omega) := by
    ext j
    simp [Finset.mem_attachFin]
  rw [h, Finset.card_attachFin, Nat.card_Icc]
  omega
end GroundTheory.Heights₂.Heights.RestTerms.HookSum
