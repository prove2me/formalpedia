-- Prove2me | solution 1 for ReciprocityTheory.Gal.cyc_eq_one_of_mem_Ine
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:22:53.167749+00:00
-- url     : https://prove2.me/submissions/1a2ece6f-0b1b-47d6-b2b9-72f5b0a8d917

import Definitions.Def_Formalism_ConjugateSelfDual_Statement
import Definitions.Def_ReciprocityTheory_GaloisValuations_GlobalA
import Definitions.Def_ReciprocityTheory_GaloisValuations_GlobalB
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Theorems.Thm_ReciprocityTheory_Gal_mem_Ine
import Theorems.Thm_ReciprocityTheory_Gal_cyc_eq_map_cycZ
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
    {σ : G F Ω} (hσ : σ ∈ Ine (F := F) A) : cyc F Ω l σ = 1 := by
  obtain ⟨-, hI⟩ := mem_Ine.mp hσ
  have key : ∀ n, PadicInt.toZModPow n ((cycZ F Ω l σ : ℤ_[l]ˣ) : ℤ_[l]) =
      PadicInt.toZModPow n ((1 : ℕ) : ℤ_[l]) :=
    cycZ_toZModPow_eq hl h (fun x hx => by simpa using hI x hx)
  have hz : ((cycZ F Ω l σ : ℤ_[l]ˣ) : ℤ_[l]) = 1 := by
    simpa using PadicInt.ext_of_toZModPow.mp key
  rw [cyc_eq_map_cycZ, show cycZ F Ω l σ = 1 from Units.ext hz, map_one]
end ReciprocityTheory.Gal
