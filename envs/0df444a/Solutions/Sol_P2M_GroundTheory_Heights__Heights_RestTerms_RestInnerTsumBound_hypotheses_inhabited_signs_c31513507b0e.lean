-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_RestInnerTsumBound_hypotheses_inhabited_signs_c31513507b0e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:08:25.505658+00:00
-- url     : https://prove2.me/submissions/c5177b53-d360-481e-9a12-e920227b0ae2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsElem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Inhabitants
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Elementary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_InhabitantsElem

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
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace RestInnerTsumBound
theorem _root_.solution :
    (2 : ℝ) ≤ 3 ∧ 1 ≤ 2 ∧ ∀ n : ℕ, |(fun n : ℕ => ((-1 : ℝ) ^ n)) n| ≤ 1 := by
  refine ⟨by norm_num, by norm_num, fun n => ?_⟩
  simp [abs_pow]
end RestInnerTsumBound
end GroundTheory.Heights₂.Heights.RestTerms
