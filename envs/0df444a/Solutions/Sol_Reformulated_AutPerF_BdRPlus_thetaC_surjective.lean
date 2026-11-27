-- Prove2me | solution 1 for Reformulated.AutPerF.BdRPlus.thetaC_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:33:18.743519+00:00
-- url     : https://prove2.me/submissions/30942625-4ecd-4f95-b241-f0ed188d6ba8

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Section
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_UniformContinuousConstSMulOfIsIsometricSMul
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Embedding
import Theorems.Thm_Reformulated_AutPerF_AinfInv_theta_surjective_of_frobenius
import Theorems.Thm_Reformulated_AutPerF_IsUnitBall_frobenius_surjective


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Ideal
open Reformulated Reformulated.AutPerF
universe u v w
variable (p : ℕ) [Fact p.Prime]
variable {C : Type u} [NormedField C] [CompleteSpace C] [CharZero C] [Fact (‖(p : C)‖ < 1)]
variable (O : ValuationSubring C) [IsUnitBall O]
open Reformulated.AutPerF.BdRPlus
variable {p O}
namespace Reformulated.AutPerF.BdRPlus
theorem _root_.solution [IsAlgClosed C] : Function.Surjective (thetaC p O) := by
  intro c
  obtain ⟨x, hx⟩ := AinfInv.theta_surjective_of_frobenius p (IsUnitBall.frobenius_surjective O p)
    ((IsUnitBall.awayEquiv O p).symm c)
  exact ⟨algebraMap _ _ x, by rw [thetaC_apply, theta_algebraMap, hx, AlgEquiv.apply_symm_apply]⟩
end Reformulated.AutPerF.BdRPlus
