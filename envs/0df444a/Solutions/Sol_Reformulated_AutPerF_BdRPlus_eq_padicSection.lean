-- Prove2me | solution 1 for Reformulated.AutPerF.BdRPlus.eq_padicSection
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:32:54.964383+00:00
-- url     : https://prove2.me/submissions/f3788223-1aba-448e-a2b3-b51b562ea006

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Section
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_UniformContinuousConstSMulOfIsIsometricSMul
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Embedding
import Theorems.Thm_Reformulated_AutPerF_BdRPlus_hom_ext_thetaC

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
variable [NormedAlgebra ℚ_[p] C]
variable [IsAlgClosed C] {L : Type w} [Field L] [Algebra ℚ_[p] L] [Algebra.IsAlgebraic ℚ_[p] L]
variable {p O}
namespace Reformulated.AutPerF
namespace BdRPlus
theorem _root_.solution (j : L →ₐ[ℚ_[p]] C) (s : L →ₐ[ℚ_[p]] BdRPlus p O)
    (h : ∀ x, BdRPlus.thetaC p O (s x) = j x) : s = BdRPlus.padicSection p O j :=
  AlgHom.coe_ringHom_injective (BdRPlus.hom_ext_thetaC (F := ℚ_[p])
    (fun a => (s.commutes a).trans ((BdRPlus.padicSection p O j).commutes a).symm)
    (fun x => (h x).trans (BdRPlus.thetaC_padicSection j x).symm))
end BdRPlus
end Reformulated.AutPerF
