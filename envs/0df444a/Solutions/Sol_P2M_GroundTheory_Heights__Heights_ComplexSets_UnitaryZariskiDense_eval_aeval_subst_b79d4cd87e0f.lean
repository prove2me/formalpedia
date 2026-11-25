-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ComplexSets_UnitaryZariskiDense_eval_aeval_subst_b79d4cd87e0f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:23:51.874935+00:00
-- url     : https://prove2.me/submissions/4b66126c-cf3e-4cbe-8f83-27b6eb3c8dff

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StUnitaryZariskiDense
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PUnitaryZariskiDense

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
open MvPolynomial Matrix Complex
noncomputable section
open GroundTheory.Heights₂.Heights.ComplexSets.UnitaryZariskiDense
namespace GroundTheory.Heights₂.Heights.ComplexSets.UnitaryZariskiDense
theorem _root_.solution {σ τ : Type*} (F : σ → MvPolynomial τ ℂ) (p : MvPolynomial σ ℂ)
    (x : τ → ℂ) : eval x (aeval F p) = eval (fun i => eval x (F i)) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add]
  | mul_X p i hp => rw [map_mul, map_mul, hp, aeval_X, map_mul, eval_X]
end GroundTheory.Heights₂.Heights.ComplexSets.UnitaryZariskiDense
