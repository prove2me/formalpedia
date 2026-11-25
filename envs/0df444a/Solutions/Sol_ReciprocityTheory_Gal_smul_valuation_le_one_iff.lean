-- Prove2me | solution 1 for ReciprocityTheory.Gal.smul_valuation_le_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:00:59.646046+00:00
-- url     : https://prove2.me/submissions/25003a4a-5734-4109-8ded-ade676f5da8b

import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Definitions.Def_ReciprocityTheory_GaloisValuations_ArithOfA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Pointwise
open ReciprocityTheory ReciprocityTheory.Gal
open Formalism.ConjugateSelfDual
variable {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
namespace ReciprocityTheory.Gal
theorem _root_.solution (γ : G F Ω) (A : ValuationSubring Ω) (y : Ω) :
    (γ • A).valuation y ≤ 1 ↔ A.valuation ((γ⁻¹ : G F Ω) y) ≤ 1 := by
  rw [ValuationSubring.valuation_le_one_iff, ValuationSubring.valuation_le_one_iff,
    ValuationSubring.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨s, hs, rfl⟩
    show γ⁻¹ • γ • s ∈ A
    rwa [inv_smul_smul]
  · intro h
    exact ⟨γ⁻¹ • y, h, smul_inv_smul γ y⟩
end ReciprocityTheory.Gal
