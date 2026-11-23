-- Prove2me | solution 1 for ReciprocityTheory.Gal.inv_mul_mem_Ine_of_isFrob
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:14:43.907594+00:00
-- url     : https://prove2.me/submissions/958e6c30-affc-495b-92f6-b0cc208899b1

import Definitions.Def_Formalism_ConjugateSelfDual_Statement
import Definitions.Def_ReciprocityTheory_GaloisValuations_GlobalA
import Definitions.Def_ReciprocityTheory_GaloisValuations_GlobalB
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Theorems.Thm_ReciprocityTheory_Gal_mem_Ine

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
variable {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
namespace ReciprocityTheory.Gal
theorem _root_.solution {A : ValuationSubring (Ω)} {q : ℕ} {σ τ : G F Ω}
    (hσ : IsFrob A q σ) (hτ : IsFrob A q τ) : σ⁻¹ * τ ∈ Ine (F := F) A := by
  obtain ⟨hσD, hσF⟩ := hσ
  obtain ⟨hτD, hτF⟩ := hτ
  have hσD' : σ ∈ Dec (F := F) A := mem_Dec.mpr hσD
  have hτD' : τ ∈ Dec (F := F) A := mem_Dec.mpr hτD
  refine mem_Ine.mpr ⟨(Dec (F := F) A).mul_mem ((Dec (F := F) A).inv_mem hσD') hτD', fun x hx => ?_⟩
  rw [← valuation_apply_lt_one_iff hσD']
  have e : σ ((σ⁻¹ * τ) x - x) = (τ x - x ^ q) - (σ x - x ^ q) := by
    rw [map_sub, AlgEquiv.mul_apply, mul_inv_apply]; ring
  rw [e]
  exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt (hτF x hx) (hσF x hx))
end ReciprocityTheory.Gal
