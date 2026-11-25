-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ComplexSets_pullback_one_b525a2fbfb79
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:53:09.170686+00:00
-- url     : https://prove2.me/submissions/d9cf7908-18fe-466c-9be5-f9b7d06cabe5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
open MvPolynomial Pointwise
noncomputable section
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.ComplexSets
theorem _root_.solution : pullback (1 : Matrix (Fin 1) (Fin 1) ℂ) = AlgHom.id ℂ _ := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  simp [pullback, linPoly]
end GroundTheory.Heights₂.Heights.ComplexSets
