-- Prove2me | solution 1 for ReciprocityTheory.Gal.isFrob_mul_of_mem_Ine
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:26:56.997929+00:00
-- url     : https://prove2.me/submissions/aa2f9511-eda6-4a9d-b8bc-c0d502edbbbe

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
theorem _root_.solution {A : ValuationSubring (Ω)} {q : ℕ} {σ ι : G F Ω}
    (hσ : IsFrob A q σ) (hι : ι ∈ Ine (F := F) A) : IsFrob A q (σ * ι) := by
  obtain ⟨hσD, hσF⟩ := hσ
  obtain ⟨hιD, hιI⟩ := mem_Ine.mp hι
  have hσD' : σ ∈ Dec (F := F) A := mem_Dec.mpr hσD
  refine ⟨mem_Dec.mp ((Dec (F := F) A).mul_mem hσD' hιD), fun x hx => ?_⟩
  have e : (σ * ι) x - x ^ q = σ (ι x - x) + (σ x - x ^ q) := by
    rw [AlgEquiv.mul_apply, map_sub]; ring
  rw [e]
  exact Valuation.map_add_lt _ ((valuation_apply_lt_one_iff hσD' _).mpr (hιI x hx)) (hσF x hx)
end ReciprocityTheory.Gal
