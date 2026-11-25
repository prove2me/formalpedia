-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SnapperDiffPoly_eval_aeval_eq_30a4cefc8185
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:59:20.33493+00:00
-- url     : https://prove2.me/submissions/7644748b-3620-41a9-8eb2-8ccf3f1051fc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperDiffPolySt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPolyOfDiffs
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperDiffPoly

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.Kleiman.SnapperDiffPoly
namespace GroundTheory.Heights₂.Heights.Kleiman.SnapperDiffPoly
theorem _root_.solution {K : Type} (x : K → ℚ) (σ : K → MvPolynomial K ℚ) (P : MvPolynomial K ℚ) :
    eval x (aeval σ P) = eval (fun k => eval x (σ k)) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p r hp hr => rw [map_add, map_add, hp, hr, map_add]
  | mul_X p j hp => simp only [map_mul, hp, aeval_X, eval_X]
end GroundTheory.Heights₂.Heights.Kleiman.SnapperDiffPoly
