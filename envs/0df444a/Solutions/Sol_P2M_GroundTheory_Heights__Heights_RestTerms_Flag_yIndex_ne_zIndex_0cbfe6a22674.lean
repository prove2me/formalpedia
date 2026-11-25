-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Flag_yIndex_ne_zIndex_0cbfe6a22674
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:52:53.574189+00:00
-- url     : https://prove2.me/submissions/3eef3ad8-34b3-4251-9b87-c000b8128953

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagBasic

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
variable {f r a : ℕ}
namespace GroundTheory.Heights₂.Heights.RestTerms.Flag
theorem _root_.solution (c : SmallBlock) (τ σ : Fin f) (l : Fin r) (i : Fin a) :
    yIndex f r a c τ l ≠ zIndex f r a c σ i := by
  cases c <;> simp only [yIndex, zIndex, ne_eq, Prod.mk.injEq, Fin.mk.injEq, not_and] <;>
    intro _ <;> omega
end GroundTheory.Heights₂.Heights.RestTerms.Flag
