-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ComplexSets_UnitaryZariskiDense_polyEval_aeval_subst_33ac81fff056
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:22:15.379637+00:00
-- url     : https://prove2.me/submissions/780248e4-ffab-48e9-948f-d80e3b8feb51

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
theorem _root_.solution {σ : Type*} (F : σ → Polynomial ℂ) (p : MvPolynomial σ ℂ) (z : ℂ) :
    (aeval F p).eval z = eval (fun i => (F i).eval z) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]
end GroundTheory.Heights₂.Heights.ComplexSets.UnitaryZariskiDense
