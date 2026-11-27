-- Prove2me | solution 1 for UpperTheory.Reformulated.B.EvaluationMap.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:32:23.261251+00:00
-- url     : https://prove2.me/submissions/d4c2435a-2a6e-43b3-8286-8880df63aebb

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_EvaluationMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

open UpperTheory.Reformulated.B.EvaluationMap.Helpers
namespace UpperTheory.Reformulated.B.EvaluationMap
theorem _root_.solution :
    ∀ {K W : Type} [inst : Group K] [inst_1 : AddCommGroup W] [inst_2 : _root_.Module ℂ W] [FiniteDimensional ℂ W]
      (ρ : Representation ℂ K W), FiniteDimensional ℂ ↥(UpperTheory.Reformulated.B.EvaluationMap.coeffSpan ρ) := by
  intro K W _ _ _ _ ρ
  have hle : UpperTheory.Reformulated.B.EvaluationMap.coeffSpan ρ ≤ LinearMap.range (Φ ρ) := by
    unfold UpperTheory.Reformulated.B.EvaluationMap.coeffSpan
    rw [Submodule.span_le]
    rintro f ⟨ℓ, w, rfl⟩
    exact ⟨evw ℓ w, rfl⟩
  exact Submodule.finiteDimensional_of_le hle
end UpperTheory.Reformulated.B.EvaluationMap
