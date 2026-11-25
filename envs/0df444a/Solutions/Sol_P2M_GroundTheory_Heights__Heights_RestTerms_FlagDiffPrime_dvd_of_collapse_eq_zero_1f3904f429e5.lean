-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_FlagDiffPrime_dvd_of_collapse_eq_zero_1f3904f429e5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:29:26.519897+00:00
-- url     : https://prove2.me/submissions/d9aa05c3-3f69-4b7b-982f-c577454350b8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsFlag
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PFlagDiffPrime
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_FlagDiffPrime_dvd_sub_collapse_fbe7a1eb7559

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
    (h : collapse a b P = 0) : (X a - X b : MvPolynomial σ ℚ) ∣ P := by
  simpa [h] using dvd_sub_collapse a b P
end GroundTheory.Heights₂.Heights.RestTerms.FlagDiffPrime
