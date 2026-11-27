-- Prove2me | solution 1 for P2M_GlobalTheory_T_integral_hasSum_eq_integral_indicator_hasSum__7c064a132370
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:49:20.919187+00:00
-- url     : https://prove2.me/submissions/2cafcc5c-fe92-4577-ba97-14e565b04bc5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralHasSumEqIntegralIndicatorHasSum
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralHasSumEqIntegralIndicatorHasSumStatement
import Theorems.Thm_GlobalTheory_integral_hasSum_eq_integral_indicator_hasSum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {X ι : Type} [MeasurableSpace X] [Countable ι] (μ : Measure X) (k : ι → X → ℂ), (∀ i, Integrable (k i) μ) → {i | ∫ x, ‖k i x‖ ∂μ ≠ 0}.Finite → ∀ (p : Set ι) (K Kp : X → ℂ), (∀ x, HasSum (fun i => k i x) (K x)) → (∀ x, HasSum (fun i => p.indicator (fun i => k i x) i) (Kp x)) → (∀ i ∉ p, ∫ x, k i x ∂μ = 0) → ∫ x, K x ∂μ = ∫ x, Kp x ∂μ := by
  first | exact @GlobalTheory.integral_hasSum_eq_integral_indicator_hasSum | exact GlobalTheory.integral_hasSum_eq_integral_indicator_hasSum | (intros; apply GlobalTheory.integral_hasSum_eq_integral_indicator_hasSum <;> assumption)
end _root_.GlobalTheory.T
