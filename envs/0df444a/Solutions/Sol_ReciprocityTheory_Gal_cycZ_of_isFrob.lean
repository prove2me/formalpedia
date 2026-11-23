-- Prove2me | solution 1 for ReciprocityTheory.Gal.cycZ_of_isFrob
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:22:52.501209+00:00
-- url     : https://prove2.me/submissions/443b97bc-ccc3-4aeb-b7f9-063de4e8b63e

import Definitions.Def_Formalism_ConjugateSelfDual_Statement
import Definitions.Def_ReciprocityTheory_GaloisValuations_GlobalA
import Definitions.Def_ReciprocityTheory_GaloisValuations_GlobalB
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Theorems.Thm_ReciprocityTheory_Gal_cycZ_toZModPow_eq

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
theorem _root_.solution [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring (Ω)}
    {v : HeightOneSpectrum (𝓞 F)} (hl : ((l : ℕ) : 𝓞 F) ∉ v.asIdeal) (h : IsPlaceOver A v)
    {σ : G F Ω} (hσ : IsFrob A (normV v) σ) : ((cycZ F Ω l σ : ℤ_[l]ˣ) : ℤ_[l]) = (normV v : ℤ_[l]) := by
  obtain ⟨-, hF⟩ := hσ
  exact PadicInt.ext_of_toZModPow.mp (cycZ_toZModPow_eq hl h hF)
end ReciprocityTheory.Gal
