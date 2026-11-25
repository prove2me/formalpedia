-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_HookSum_hookShape_isHook_13714c2e5d51
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:52:57.370161+00:00
-- url     : https://prove2.me/submissions/f7763101-78b4-4ace-a9d2-418a69812c25

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
theorem _root_.solution (r k l : ℕ) : ∀ i : Fin r, (i : ℕ) ≠ 0 → hookShape r k l i ≤ 1 := by
  intro i hi
  simp only [hookShape]
  split_ifs <;> omega
end GroundTheory.Heights₂.Heights.RestTerms.HookSum
