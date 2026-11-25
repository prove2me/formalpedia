-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Comb_stair_strictAnti_de0ce4e394a3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:24:29.154819+00:00
-- url     : https://prove2.me/submissions/2a154ac8-0246-4df2-8c6e-eab537abbc18

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsComb
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCombCfAtStair

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
open MvPolynomial Finset Equiv Comb
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace Comb
theorem _root_.solution (m : ℕ) : StrictAnti (stair m) := by
  intro a b hab
  have hb := b.isLt
  have hab' : (a : ℕ) < b := hab
  simp only [stair]
  omega
end Comb
end GroundTheory.Heights₂.Heights.RestTerms
