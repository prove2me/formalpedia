-- Prove2me | solution 1 for P2M_GlobalTheory_T_valuation_embedding_generator_eq_one__0e3284c94f64
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:52:46.779913+00:00
-- url     : https://prove2.me/submissions/c814f45f-3a42-453b-ba5c-1085197f34d6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ValuationEmbeddingGeneratorEqOne
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ValuationEmbeddingGeneratorEqOneStatement
import Theorems.Thm_GlobalTheory_valuation_embedding_generator_eq_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : Type) [Field K] [NumberField K] (A : ValuationSubring ℂ) (p : ℕ), p.Prime → (p : ℂ) ∈ A.nonunits → ∀ (P : HeightOneSpectrum (𝓞 K)), (p : 𝓞 K) ∉ P.asIdeal → ∀ (α : 𝓞 K) (h : ℕ), Ideal.span {α} = P.asIdeal ^ h → ∀ σ : K →+* ℂ, A.valuation (σ (α : K)) = 1 := by
  first | exact @GlobalTheory.valuation_embedding_generator_eq_one | exact GlobalTheory.valuation_embedding_generator_eq_one | (intros; apply GlobalTheory.valuation_embedding_generator_eq_one <;> assumption)
end _root_.GlobalTheory.T
