-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Flag_psum_mem_range_c0a256d7f214
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:52:22.491615+00:00
-- url     : https://prove2.me/submissions/e935b6fc-94d5-4a1a-93a9-0cb571d6886e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PowerSums

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
open GroundTheory.Heights₂.Heights.RestTerms.Flag
open MvPolynomial Finset
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms.Flag
theorem _root_.solution (N j : ℕ) (hj1 : 1 ≤ j) (hjN : j ≤ N) :
    psum (Fin N) ℚ j ∈ (powerSumHom N).range := by
  refine ⟨X ⟨j - 1, by omega⟩, ?_⟩
  change powerSumHom N (X ⟨j - 1, by omega⟩) = _
  simp only [powerSumHom, aeval_X]
  congr 1
  show j - 1 + 1 = j
  omega
end GroundTheory.Heights₂.Heights.RestTerms.Flag
