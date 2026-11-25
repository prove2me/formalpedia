-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.integralClosureRank_and_residueTrdegLe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:24:07.897544+00:00
-- url     : https://prove2.me/submissions/308b2717-9c1a-4ec6-a103-6498e830bfc3

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_ComapInclusionIsLocalHom
import Definitions.Def_ReciprocityTheory_SemistableReduction_IntegralClosureRankAndResidueTrdegLe
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_integralClosureRank
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_residueTrdegLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MvPolynomial
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution : DedekindRankStatement ∧ TRStatement :=
  ⟨by intro O F L; intros; exact integralClosureRank O F L, residueTrdegLe⟩
end ReciprocityTheory.MultiplicativeHeights
