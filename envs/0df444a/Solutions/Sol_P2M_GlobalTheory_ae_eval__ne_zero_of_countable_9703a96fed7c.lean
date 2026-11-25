-- Prove2me | solution 1 for P2M_GlobalTheory_ae_eval__ne_zero_of_countable_9703a96fed7c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:09:53.873017+00:00
-- url     : https://prove2.me/submissions/d103960d-9a1a-40a3-8c44-c0ffd307762e

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_AeBlockSphereEvalNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_AeTranscendentalPointNonvanishing
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_ae_eval_ne_zero_linear


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (K : Type) [Field K] [Countable K] (σ : K →+* ℂ)
    (ι : Type) [Fintype ι] :
    ∀ᵐ t : ι → ℂ, ∀ Q : MvPolynomial ι K, Q ≠ 0 → MvPolynomial.eval₂ σ t Q ≠ 0 := by
  have : Countable (MvPolynomial ι K) :=
    (MvPolynomial.basisMonomials ι K).repr.injective.countable
  rw [ae_all_iff]
  intro Q
  by_cases hQ : Q = 0
  · exact Filter.Eventually.of_forall fun t h => absurd hQ h
  · have hm : MvPolynomial.map σ Q ≠ 0 := by
      intro h
      exact hQ (MvPolynomial.map_injective σ σ.injective (by rw [h, map_zero]))
    have h := ReciprocityTheory.MultiplicativeHeights.ae_eval_ne_zero_linear (volume : Measure (ι → ℂ))
      (LinearEquiv.refl ℂ (ι → ℂ)) _ hm
    filter_upwards [h] with t ht _
    rw [MvPolynomial.eval₂_eq_eval_map]
    exact ht
end GlobalTheory
