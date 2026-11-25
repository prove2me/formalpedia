-- Prove2me | solution 1 for P2M_Formalism_LT_LTL_mem_span_of_norm_le__498e07ccaf2e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:52:54.155283+00:00
-- url     : https://prove2.me/submissions/f2dca9ee-dd89-4055-a70d-a950d0d44732

import Definitions.Def_Formalism_TorsionNormIteration_LTLemma
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_InvInt
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_MemSpanOfNormLe
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_LTLemma

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
universe u
open Formalism Formalism.LT Formalism.LT.LTL
open Formalism.G Formalism.G.LogCR Formalism.LT.InvIntP
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
namespace Formalism.LT.LTL
theorem _root_.solution {π : K} (hπ : ‖π‖ ≤ 1) (hπ0 : π ≠ 0) (x : unitBall K)
    (hx : ‖(x : K)‖ ≤ ‖π‖) : x ∈ Ideal.span {piO π hπ} := by
  rw [Ideal.mem_span_singleton']
  have hc : ‖(x : K) / π‖ ≤ 1 := by
    rw [norm_div]
    exact div_le_one_of_le₀ hx (norm_nonneg _)
  refine ⟨⟨(x : K) / π, hc⟩, ?_⟩
  apply Subtype.ext
  rw [Subring.coe_mul]
  change (x : K) / π * π = x
  field_simp
end Formalism.LT.LTL
