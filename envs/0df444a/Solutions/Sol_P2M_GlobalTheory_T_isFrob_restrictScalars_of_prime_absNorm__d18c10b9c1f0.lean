-- Prove2me | solution 1 for P2M_GlobalTheory_T_isFrob_restrictScalars_of_prime_absNorm__d18c10b9c1f0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:33:52.184454+00:00
-- url     : https://prove2.me/submissions/26e923c5-1ff4-46a5-8e1e-ff64772adbe7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsFrobRestrictScalarsOfPrimeAbsNorm
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsFrobRestrictScalarsOfPrimeAbsNormStatement
import Theorems.Thm_GlobalTheory_isFrob_restrictScalars_of_prime_absNorm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (Z : IntermediateField F Ω) [NumberField Z] (w : HeightOneSpectrum (𝓞 Z)) (v : HeightOneSpectrum (𝓞 F)), w.asIdeal.LiesOver v.asIdeal → (Ideal.absNorm w.asIdeal).Prime → ∀ B : ValuationSubring Ω, IsPlaceOver (F := Z) B w → ∀ σ : G Z Ω, IsFrob B (normV w) σ → Ideal.absNorm v.asIdeal = Ideal.absNorm w.asIdeal ∧ IsPlaceOver (F := F) B v ∧ IsFrob (F := F) B (normV v) (σ.restrictScalars F) := by
  first | exact @GlobalTheory.isFrob_restrictScalars_of_prime_absNorm | exact GlobalTheory.isFrob_restrictScalars_of_prime_absNorm | (intros; apply GlobalTheory.isFrob_restrictScalars_of_prime_absNorm <;> assumption)
end _root_.GlobalTheory.T
