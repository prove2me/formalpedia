-- Prove2me | solution 1 for PI.WickFormula.ordLin_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:18:47.398061+00:00
-- url     : https://prove2.me/submissions/1007e7b8-b6de-4e20-9e1f-09860af130c9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_DeltaEqGdelta
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_OrdEvalEqSumOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open PI PI.WickFormula
namespace PI.WickFormula
theorem _root_.solution : OrdLin := by
  intro k AA _ _ _ r s a a'
  exact ⟨ordL k a a', fun P => rfl⟩
end PI.WickFormula
