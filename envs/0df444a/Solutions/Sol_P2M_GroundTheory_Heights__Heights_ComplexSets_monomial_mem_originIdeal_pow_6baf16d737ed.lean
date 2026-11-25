-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ComplexSets_monomial_mem_originIdeal_pow_6baf16d737ed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:52:44.435901+00:00
-- url     : https://prove2.me/submissions/f809962a-3fe4-4eda-8b06-187183101f71

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StConeAvoidsOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeAvoidsOpen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
open MvPolynomial
noncomputable section
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.ComplexSets
theorem _root_.solution {N : ℕ} {m : Fin n →₀ ℕ} (hm : m.degree = N) :
    monomial m (1 : ℂ) ∈ originIdeal n ^ N := by
  have hprod : ∏ i ∈ m.support, (X i : MvPolynomial (Fin n) ℂ) ^ m i = ∏ i, X i ^ m i :=
    Finset.prod_subset (Finset.subset_univ _) fun i _ hi => by simp [Finsupp.notMem_support_iff.1 hi]
  rw [← prod_X_pow_eq_monomial, hprod, ← hm, Finsupp.degree_eq_sum, ← Finset.prod_pow_eq_pow_sum]
  exact Ideal.prod_mem_prod fun i _ => Ideal.pow_mem_pow
    (show (X i : MvPolynomial (Fin n) ℂ) ∈ originIdeal n from Ideal.subset_span ⟨i, rfl⟩) _
end GroundTheory.Heights₂.Heights.ComplexSets
