-- Prove2me | solution 1 for P2M_Formalism_LT_LTL_norm_le_of_mem_span__3b10f192d90f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:52:54.959681+00:00
-- url     : https://prove2.me/submissions/cbcbc23b-7441-497d-b3ff-4d8ee21aa97a

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
theorem _root_.solution {π : K} (hπ : ‖π‖ ≤ 1) (x : unitBall K)
    (hx : x ∈ Ideal.span {piO π hπ}) : ‖(x : K)‖ ≤ ‖π‖ := by
  rw [Ideal.mem_span_singleton'] at hx
  obtain ⟨c, rfl⟩ := hx
  have hc : ‖(c : K)‖ ≤ 1 := c.2
  rw [Subring.coe_mul, norm_mul]
  calc ‖(c : K)‖ * ‖π‖ ≤ 1 * ‖π‖ := by gcongr
    _ = ‖π‖ := one_mul _
end Formalism.LT.LTL
