-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__GatR_mem_span_om_pow_bf8597fdd0ae
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:30:52.161118+00:00
-- url     : https://prove2.me/submissions/fa9db13c-7267-4d19-aba2-185332af0795

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_GatRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.GatR
open QuadraticAlgebra IsLocalRing
variable {W : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] {ϖ : W}
namespace Formalism.BasicNotions.Examples₂.GatR
theorem _root_.solution (m : ℕ) (z : QuadraticAlgebra W ϖ 0) :
    z ∈ Ideal.span {(ω : QuadraticAlgebra W ϖ 0) ^ (2 * m)} ↔ ϖ ^ m ∣ z.re ∧ ϖ ^ m ∣ z.im := by
  rw [Ideal.mem_span_singleton, om_pow, algebraMap_eq]
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨⟨t.re, by simp⟩, ⟨t.im, by simp⟩⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    exact ⟨⟨a, b⟩, by ext <;> simp [ha, hb]⟩
end Formalism.BasicNotions.Examples₂.GatR
