-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Coinv_psumIdeal_rat_eq_1ba39560cb25
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:50:33.518278+00:00
-- url     : https://prove2.me/submissions/faf6b6ad-8ab2-4054-a56b-5ad748767d68

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsCoinv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCoinvariantTopDegree

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
open MvPolynomial Finset
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace Coinv
theorem _root_.solution (f N : ℕ) :
    Coinv.psumIdeal ℚ f N =
      Ideal.span {P | ∃ k τ, 1 ≤ k ∧ k ≤ N ∧ P = blockPowerSum f N k τ} := rfl
end Coinv
end GroundTheory.Heights₂.Heights.RestTerms
