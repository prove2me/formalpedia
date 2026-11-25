-- Prove2me | solution 1 for P2M_GlobalTheory_hasSum_of_dominated_of_eq_near_zero__09c68aa174a9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:34:00.43706+00:00
-- url     : https://prove2.me/submissions/ba1adcae-85d1-44ea-97cc-713a3bdd3b86

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasSumOfDominatedOfEqNearZero
import Theorems.Thm_GlobalTheory_hasSum_of_dominated_of_eq_near_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric Filter Topology
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ {ι : Type} (b : ι → ℂ) (c : ι → ℝ) (n : ι → ℕ) (R : ℂ → ℂ) (r ε : ℝ), (∀ i, ‖b i‖ ≤ c i) →
    (∀ x : ℝ, 0 ≤ x → x < r → Summable (fun i => c i * x ^ n i)) → 0 < ε →
    DifferentiableOn ℂ R (Metric.ball 0 r) →
    (∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < ε → HasSum (fun i => b i * z ^ n i) (R z)) →
    ∀ z : ℂ, ‖z‖ < r → HasSum (fun i => b i * z ^ n i) (R z) :=
  fun b c n R r ε h1 h2 h3 h4 h5 => hasSum_of_dominated_of_eq_near_zero b c n R r ε h1 h2 h3 h4 h5
end GlobalTheory
