-- Prove2me | solution 1 for UpperTheory.Reformulated.B.Yyc2.dual_mem_span_eval_of_finiteDimensional
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:55:43.826612+00:00
-- url     : https://prove2.me/submissions/8aaefc55-b9fa-4b41-9d3c-90ac6374b80b

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DualMemSpanEvalOfFiniteDimensional

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Yyc2
theorem _root_.solution :
    ∀ {Y : Type} (E : Submodule ℂ (Y → ℂ)) [FiniteDimensional ℂ ↥E] (φ : Module.Dual ℂ ↥E),
      φ ∈ Submodule.span ℂ (Set.range fun (y : Y) ↦ LinearMap.proj y ∘ₗ E.subtype) := by
  intro Y E _ φ
  apply FiniteDimensional.mem_span_of_iInf_ker_le_ker
  intro x hx
  have h0 : x = 0 := by
    apply Subtype.ext
    funext y
    exact (Submodule.mem_iInf _).1 hx y
  rw [h0]
  exact Submodule.zero_mem _
end UpperTheory.Reformulated.B.Yyc2
