-- Prove2me | solution 1 for ReciprocityTheory.Gal.not_valuation_lt_one_of_isPlaceOver
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:14:44.35584+00:00
-- url     : https://prove2.me/submissions/b28d16c8-0ed1-4109-9fec-047447ddce1d

import Definitions.Def_Formalism_ConjugateSelfDual_Statement
import Definitions.Def_ReciprocityTheory_GaloisValuations_GlobalA
import Definitions.Def_ReciprocityTheory_GaloisValuations_GlobalB
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global

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
theorem _root_.solution {l : ℕ} {A : ValuationSubring (Ω)}
    {v : HeightOneSpectrum (𝓞 F)} (hl : ((l : ℕ) : 𝓞 F) ∉ v.asIdeal) (h : IsPlaceOver A v)
    (n : ℕ) : ¬ A.valuation (((l ^ n : ℕ) : Ω)) < 1 := by
  unfold Formalism.ConjugateSelfDual.IsPlaceOver at h
  intro hlt
  have hc : algebraMap F Ω (((l ^ n : ℕ) : 𝓞 F) : F) = ((l ^ n : ℕ) : Ω) := by
    simp
  rw [← hc, h] at hlt
  exact hl (v.isPrime.mem_of_pow_mem n (by simpa using hlt))
end ReciprocityTheory.Gal
