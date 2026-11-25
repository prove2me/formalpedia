-- Prove2me | solution 1 for PositivityTheory.ThK.SiegelT.boxL_box
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:58:00.556334+00:00
-- url     : https://prove2.me/submissions/2f7bbaa8-9156-4c25-9259-6f0acdbedc5f

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_SiegelTransportAn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThK PositivityTheory.ThK.SiegelT
open Matrix GlobalTheory.WeilM Topology Filter
variable {R : Type} [TopologicalSpace R] [T2Space R] {κ κ' : Type}
namespace PositivityTheory.ThK.SiegelT
theorem _root_.solution {A : Type} (l : ((κ → A) → ℂ) →ₗ[ℂ] ℂ) (l' : ((κ' → A) → ℂ) →ₗ[ℂ] ℂ) (φ₁ : (κ → A) → ℂ) (φ₂ : (κ' → A) → ℂ) :
    boxL l l' (fun x => φ₁ (x ∘ Sum.inl) * φ₂ (x ∘ Sum.inr)) = l φ₁ * l' φ₂ := by
  show l' _ = _
  rw [← smul_eq_mul, ← map_smul]
  congr 1
  funext y
  rw [Pi.smul_apply, smul_eq_mul, mul_comm, ← smul_eq_mul, ← map_smul]
  congr 1
  funext x
  exact mul_comm _ _
end PositivityTheory.ThK.SiegelT
