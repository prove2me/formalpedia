-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_StepThreeOnWLift_twist_idealSys_eq_904493232767
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:27:02.693945+00:00
-- url     : https://prove2.me/submissions/e9657f87-099b-4e1e-8fa2-57fee48e7cf4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepThreeOnWLift
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsClaimSeq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PClaimVanish
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSurjectiveClosed
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PStepThreeOnWLift
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_StepThreeOnWLift_idealGraded_tildeSys_7efc367dd016
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SurjectiveClosed_twist_sub_eq_mul_482b06edabb9


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
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.StepThreeOnWLift
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman.StepThreeOnWLift
theorem _root_.solution (Q : SubSystem k x Ω) (P : Ideal (Poly k N)) :
    Q.twist (idealSys x P) = ((idealGraded x P).tildeSys 0).twist Q := by
  rw [idealGraded_tildeSys]
  refine SubSystem.ext_sub fun I => ?_
  rw [SurjectiveClosed.twist_sub_eq_mul, SurjectiveClosed.twist_sub_eq_mul, mul_comm]
end GroundTheory.Heights₂.Heights.Kleiman.StepThreeOnWLift
