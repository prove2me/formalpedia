-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_aeval_mem_pow_9aee5e0ba8ce
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:30:49.308814+00:00
-- url     : https://prove2.me/submissions/2bff4e30-8650-40a9-80ce-f81c76f7e319

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_NotTwistFiniteAtZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ImportsBisAltAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistPowZeroSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
open MvPolynomial
variable {S : Type} [CommRing S] {N : ℕ} {Ω : Type} [Field Ω] [Algebra S Ω] {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
theorem _root_.solution {r : ℕ} {Q : Submodule S Ω} {η : Fin (r + 1) → Ω} (hη : ∀ j, η j ∈ Q)
    {f : MvPolynomial (Fin (r + 1)) S} {e : ℕ} (hf : f.IsHomogeneous e) : aeval η f ∈ Q ^ e := by
  have hmon : ∀ (d : Fin (r + 1) →₀ ℕ) (t : Finset (Fin (r + 1))),
      ∏ j ∈ t, η j ^ d j ∈ Q ^ (∑ j ∈ t, d j) := by
    intro d t
    induction t using Finset.induction_on with
    | empty =>
      simp only [Finset.prod_empty, Finset.sum_empty, pow_zero]
      exact Submodule.mem_one.mpr ⟨1, map_one _⟩
    | insert j t hj ih =>
      rw [Finset.prod_insert hj, Finset.sum_insert hj, pow_add]
      exact Submodule.mul_mem_mul (Submodule.pow_mem_pow _ (hη j) _) ih
  rw [f.as_sum, map_sum]
  refine Submodule.sum_mem _ fun d hd => ?_
  rw [aeval_monomial, ← Algebra.smul_def]
  refine Submodule.smul_mem _ _ ?_
  have hdeg : Finsupp.degree d = e := by
    rw [Finsupp.degree_eq_weight_one]
    exact hf (mem_support_iff.mp hd)
  have := hmon d d.support
  rw [show (∑ j ∈ d.support, d j) = e from hdeg] at this
  exact this
end GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
