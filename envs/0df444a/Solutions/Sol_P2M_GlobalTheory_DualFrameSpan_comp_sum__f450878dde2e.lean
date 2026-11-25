-- Prove2me | solution 1 for P2M_GlobalTheory_DualFrameSpan_comp_sum__f450878dde2e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:31:33.840829+00:00
-- url     : https://prove2.me/submissions/9d259b9a-4209-435c-8631-44fe6415a5b9

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
    g ∘ₗ (∑ i ∈ s, f i) = ∑ i ∈ s, g ∘ₗ f i := by
  ext x; simp [LinearMap.sum_apply]
end GlobalTheory.DualFrameSpan
