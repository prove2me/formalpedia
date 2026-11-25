-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PrimeQuasiFiniteSheets_eval_pullback_877f341acccc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:47:30.167387+00:00
-- url     : https://prove2.me/submissions/c675634e-8f8e-489c-b6ef-9c6216729efb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsPrimeQuasiFiniteSheets
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsFiniteFibresDimLe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StDominantPrimitiveFibres
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSimpleRootBranch
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PPrimeQuasiFiniteSheets

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
open GroundTheory.Heights₂.Heights.PrimeQuasiFiniteSheets
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.PrimeQuasiFiniteSheets
theorem _root_.solution (A : Matrix (Fin d) (Fin n) ℂ) (x : Fin n → ℂ) (g : MvPolynomial (Fin d) ℂ) :
    eval x (ComplexSets.pullback A g) = eval (A.mulVec x) g := by
  induction g using MvPolynomial.induction_on with
  | C a => simp [ComplexSets.pullback]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp]
    congr 1
    simp [ComplexSets.pullback, ComplexSets.linPoly, Matrix.mulVec, dotProduct]
end GroundTheory.Heights₂.Heights.PrimeQuasiFiniteSheets
