-- Prove2me | solution 1 for ReciprocityTheory.Neutral.Cmp.lies_over_ratPrime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:09:47.235018+00:00
-- url     : https://prove2.me/submissions/236239de-1b42-47ed-aa74-6d74d6fef809

import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_Kloc
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_ValuationIntCastLtOneIff
import Theorems.Thm_ReciprocityTheory_Neutral_Cmp_valuation_intCast_lt_one_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.Neutral ReciprocityTheory.Neutral.Cmp
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain
open scoped Pointwise
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {p : ℕ} [Fact p.Prime]
namespace ReciprocityTheory.Neutral.Cmp
theorem _root_.solution [CharZero Ω] (B : ValuationSubring Ω) (hp : B.valuation (p : Ω) < 1) (x : 𝓞 ℚ) :
    B.valuation (algebraMap ℚ Ω (x : ℚ)) < 1 ↔ x ∈ (ratPrime p).asIdeal := by
  have hx : (x : ℚ) = ((Rat.ringOfIntegersEquiv x : ℤ) : ℚ) := by
    conv_lhs => rw [← Rat.ringOfIntegersEquiv.symm_apply_apply x]
    simp
  rw [hx, map_intCast, valuation_intCast_lt_one_iff B hp]
  show _ ↔ Rat.ringOfIntegersEquiv x ∈ Ideal.span {(p : ℤ)}
  rw [Ideal.mem_span_singleton]
end ReciprocityTheory.Neutral.Cmp
