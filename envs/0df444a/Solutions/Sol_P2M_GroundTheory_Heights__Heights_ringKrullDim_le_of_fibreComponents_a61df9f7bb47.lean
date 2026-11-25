-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ringKrullDim_le_of_fibreComponents_a61df9f7bb47
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:36:38.095477+00:00
-- url     : https://prove2.me/submissions/45c7598d-edae-412f-87df-631ab9e83d16

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_StatementsFibreCompDimZ
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_OfChartPointSecPointSpecChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_FiniteIntegralClosureCharZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PFibreCompDimZ
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ringKrullDim_quotient_le_of_minimalPrimes_1b7b2c331aa3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_isJacobsonRing_int_5cab28bc29cb


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial IsDedekindDomain
variable {σ : Type} [Fintype σ] {P : Ideal (MvPolynomial σ ℤ)}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (k : WithBot ℕ∞)
    (h : ∀ q : ℕ, q.Prime → ∀ W ∈ (P ⊔ Ideal.span {(C (q : ℤ) : MvPolynomial σ ℤ)}).minimalPrimes,
      ringKrullDim (MvPolynomial σ ℤ ⧸ W) ≤ k) :
    ringKrullDim (MvPolynomial σ ℤ ⧸ P) ≤ k + 1 := by
  rw [ringKrullDim_le_iff_isMaximal_height_le]
  intro M hM
  have := Model.isJacobsonRing_int
  let := Ideal.Quotient.field M
  let g : MvPolynomial σ ℤ →+* (MvPolynomial σ ℤ ⧸ P) ⧸ M :=
    (Ideal.Quotient.mk M).comp (Ideal.Quotient.mk P)
  have hg : Function.Surjective g := Ideal.Quotient.mk_surjective.comp Ideal.Quotient.mk_surjective
  have hI := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' (g.comp C)
    (MvPolynomial.comp_C_integral_of_surjective_of_isJacobsonRing g hg) ⊥
  obtain ⟨q, hq, hqI⟩ := (Ideal.isPrime_int_iff.mp hI.isPrime).resolve_left
    (Ring.ne_bot_of_isMaximal_of_not_isField hI Int.not_isField)
  have hqM : Ideal.Quotient.mk P (C (q : ℤ)) ∈ M := by
    have : (q : ℤ) ∈ (⊥ : Ideal ((MvPolynomial σ ℤ ⧸ P) ⧸ M)).comap (g.comp C) := by
      rw [hqI]
      exact Ideal.subset_span rfl
    rwa [Ideal.mem_comap, Ideal.mem_bot, RingHom.comp_apply, RingHom.comp_apply,
      Ideal.Quotient.eq_zero_iff_mem] at this
  refine (Ideal.height_le_ringKrullDim_quotient_add_one hqM).trans (add_le_add_left ?_ 1)
  have hspan : Ideal.span {Ideal.Quotient.mk P (C (q : ℤ))} =
      (Ideal.span {(C (q : ℤ) : MvPolynomial σ ℤ)}).map (Ideal.Quotient.mk P) := by
    rw [Ideal.map_span, Set.image_singleton]
  rw [hspan, ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotSup P _)]
  exact ringKrullDim_quotient_le_of_minimalPrimes _ _ (h q hq)
end GroundTheory.Heights₂.Heights
