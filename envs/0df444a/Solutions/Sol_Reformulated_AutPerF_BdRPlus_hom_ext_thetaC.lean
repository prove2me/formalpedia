-- Prove2me | solution 1 for Reformulated.AutPerF.BdRPlus.hom_ext_thetaC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:01:44.326544+00:00
-- url     : https://prove2.me/submissions/a5e8f5a6-2305-4db7-9c11-14233f3c264f

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Section
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_UniformContinuousConstSMulOfIsIsometricSMul
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Embedding
import Theorems.Thm_Reformulated_AutPerF_BdRPlus_hom_ext_of_formallyUnramified
import Theorems.Thm_Reformulated_AutPerF_formallyEtale_of_isAlgebraic


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
theorem _root_.solution {F : Type v} {L : Type w} [Field F] [Field L] [Algebra F L] [CharZero F]
    [Algebra.IsAlgebraic F L] {s₁ s₂ : L →+* BdRPlus p O}
    (hF : ∀ a : F, s₁ (algebraMap F L a) = s₂ (algebraMap F L a))
    (hθ : ∀ x, thetaC p O (s₁ x) = thetaC p O (s₂ x)) : s₁ = s₂ :=
  haveI := formallyEtale_of_isAlgebraic F L
  hom_ext_of_formallyUnramified hF fun x => (IsUnitBall.awayEquiv O p).injective (hθ x)
end Reformulated.AutPerF.BdRPlus
