-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_FlagVandermondeDvd_blockSign_update_swap_540d64528759
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:51:48.040233+00:00
-- url     : https://prove2.me/submissions/5f04e8cc-4c91-4e67-afba-0344c3092643

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsFlag
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PFlagVandermondeDvd

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
open GroundTheory.Heights₂.Heights.RestTerms.FlagVandermondeDvd
namespace GroundTheory.Heights₂.Heights.RestTerms.FlagVandermondeDvd
theorem _root_.solution (f N : ℕ) (τ : Fin f) (i j : Fin N) (hij : i ≠ j) :
    blockSign f N (Function.update 1 τ (Equiv.swap i j)) = -1 := by
  unfold blockSign
  rw [Fintype.prod_eq_single τ]
  · simp [Equiv.Perm.sign_swap hij]
  · intro σ hσ
    simp [Function.update_of_ne hσ]
end GroundTheory.Heights₂.Heights.RestTerms.FlagVandermondeDvd
