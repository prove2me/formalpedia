-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_CombCfBound_alternantPsum_cons_28c4eecdeac9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:23:02.82834+00:00
-- url     : https://prove2.me/submissions/cff66010-894f-4866-9038-011f066430fc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsComb
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCombCfBound

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
noncomputable section
open GroundTheory.Heights₂.Heights.RestTerms.CombCfBound
namespace GroundTheory.Heights₂.Heights.RestTerms.CombCfBound
theorem _root_.solution (m q : ℕ) (ρ : List ℕ) :
    alternantPsum m (q :: ρ) = alternantPsum m ρ * psum (Fin m) ℚ q := by
  unfold alternantPsum
  simp only [List.map_cons, List.prod_cons]
  ring
end GroundTheory.Heights₂.Heights.RestTerms.CombCfBound
