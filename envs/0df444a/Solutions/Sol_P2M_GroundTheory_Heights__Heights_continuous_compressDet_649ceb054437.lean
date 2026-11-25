-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_continuous_compressDet_649ceb054437
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:29:55.972248+00:00
-- url     : https://prove2.me/submissions/59b91937-d921-47fa-aa9e-e0c2074a5f45

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeJacMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsTangentJacCompress
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsKernelProjMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeTangentAverage
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeJacMeasurable
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_continuous_gramOp_91b5319593a9

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Module
noncomputable section
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (m : ℕ) :
    Continuous fun p : (Fin m → Fin n → ℂ) ×
      (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) => compressDet p.1 p.2 :=
  Complex.continuous_re.comp (ContinuousLinearMap.continuous_det.comp
    ((continuous_snd.clm_comp (((continuous_gramOp m).comp continuous_fst).clm_comp
      continuous_snd)).add (continuous_const.sub continuous_snd)))
end GroundTheory.Heights₂.Heights
