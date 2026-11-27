-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Comb_inh_standard_two_one_93972da74e08
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:08:29.698363+00:00
-- url     : https://prove2.me/submissions/5dbfce0f-722f-4eec-bd0a-e29b1043dcb6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsComb
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_InhabitantsComb

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
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace Comb
theorem _root_.solution : IsStandard inhNumbering := by
  intro p q h1 h2
  change ((inhNumberingFun p : ℕ)) ≤ (inhNumberingFun q : ℕ)
  revert p q
  unfold inhNumberingFun
  decide
end Comb
end GroundTheory.Heights₂.Heights.RestTerms
