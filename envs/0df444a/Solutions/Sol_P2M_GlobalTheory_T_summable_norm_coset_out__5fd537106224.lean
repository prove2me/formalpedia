-- Prove2me | solution 1 for P2M_GlobalTheory_T_summable_norm_coset_out__5fd537106224
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:54:34.374101+00:00
-- url     : https://prove2.me/submissions/2966fe09-0d41-489c-b6b6-6c58ee10fe62

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SummableNormCosetOut
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SummableNormCosetOutStatement
import Theorems.Thm_GlobalTheory_summable_norm_coset_out


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
theorem _root_.solution : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant] (K : Subgroup G), IsOpen (K : Set G) → μ K = 1 → ∀ F : G → ℂ, (∀ g, ∀ k ∈ K, F (g * k) = F g) → Integrable F μ → Summable (fun x : G ⧸ K => ‖F x.out‖) := by
  first | exact @GlobalTheory.summable_norm_coset_out | exact GlobalTheory.summable_norm_coset_out | (intros; apply GlobalTheory.summable_norm_coset_out <;> assumption)
end _root_.GlobalTheory.T
