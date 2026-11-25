-- Prove2me | solution 1 for P2M_GlobalTheory_DualFrameSpan_sum_comp__71b2899da374
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:31:37.273342+00:00
-- url     : https://prove2.me/submissions/b963f429-643b-4030-88a0-7dc6e58e9108

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsDualFrameSpanUnitaryRepresentation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open GlobalTheory GlobalTheory.DualFrameSpan
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
namespace GlobalTheory.DualFrameSpan
theorem _root_.solution {ι : Type} (s : Finset ι) (f : ι → (H →ₗ[ℂ] H)) (g : H →ₗ[ℂ] H) :
    (∑ i ∈ s, f i) ∘ₗ g = ∑ i ∈ s, f i ∘ₗ g := by
  ext x; simp [LinearMap.sum_apply]
end GlobalTheory.DualFrameSpan
