-- Prove2me | solution 1 for P2M_GlobalTheory_T_valuation_sqrt_absNorm_eq_one__72ad47624d04
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:52:56.33043+00:00
-- url     : https://prove2.me/submissions/af8641f4-b4cc-4a6d-9ce8-15a775d4820f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ValuationSqrtAbsNormEqOne
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ValuationSqrtAbsNormEqOneStatement
import Theorems.Thm_GlobalTheory_valuation_sqrt_absNorm_eq_one


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
theorem _root_.solution : ∀ (K : Type) [Field K] [NumberField K] (A : ValuationSubring ℂ) (p : ℕ), p.Prime → (p : ℂ) ∈ A.nonunits → ∀ (P : HeightOneSpectrum (𝓞 K)), (p : 𝓞 K) ∉ P.asIdeal → A.valuation (((Real.sqrt (Ideal.absNorm P.asIdeal) : ℝ) : ℂ)) = 1 := by
  first | exact @GlobalTheory.valuation_sqrt_absNorm_eq_one | exact GlobalTheory.valuation_sqrt_absNorm_eq_one | (intros; apply GlobalTheory.valuation_sqrt_absNorm_eq_one <;> assumption)
end _root_.GlobalTheory.T
