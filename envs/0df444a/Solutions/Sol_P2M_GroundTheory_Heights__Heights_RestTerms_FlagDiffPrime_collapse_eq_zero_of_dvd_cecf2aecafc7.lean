-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_FlagDiffPrime_collapse_eq_zero_of_dvd_cecf2aecafc7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:51:44.349254+00:00
-- url     : https://prove2.me/submissions/1c297ead-5b9f-469c-a991-5e02ca18d07b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsFlag
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PFlagDiffPrime
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_FlagDiffPrime_collapse_X_sub_1f06c67bc04a

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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.RestTerms.FlagDiffPrime
variable {σ : Type} [DecidableEq σ]
namespace GroundTheory.Heights₂.Heights.RestTerms.FlagDiffPrime
theorem _root_.solution (a b : σ) {P : MvPolynomial σ ℚ}
    (h : (X a - X b : MvPolynomial σ ℚ) ∣ P) : collapse a b P = 0 := by
  obtain ⟨c, rfl⟩ := h
  rw [map_mul, collapse_X_sub, zero_mul]
end GroundTheory.Heights₂.Heights.RestTerms.FlagDiffPrime
