-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__LB_mem_nclo_3cc3277ee635
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:52:59.13941+00:00
-- url     : https://prove2.me/submissions/bc60bd5c-f8cf-4017-ac78-a040bcba979c

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NDLocC
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CovariantDegrees
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NDLocD

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.LB
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Pointwise Formalism.BasicNotions Formalism.BasicNotions.Loc
variable {l : ℕ} [hl : Fact l.Prime] {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
  [IsAlgClosure E Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {j : Ω →+* PadicAlgCl l}
  {A : ValuationSubring Ω} (hj : ∀ x, x ∈ A ↔ ‖j x‖ ≤ 1)
namespace Formalism.BasicNotions.Examples₂.LB
theorem _root_.solution (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K]
    (τ : ↥K →ₐ[ℚ_[l]] Om l) (x : ↥K) : τ x ∈ (nclo K).1 :=
  τ.fieldRange_le_normalClosure ⟨x, rfl⟩
end Formalism.BasicNotions.Examples₂.LB
