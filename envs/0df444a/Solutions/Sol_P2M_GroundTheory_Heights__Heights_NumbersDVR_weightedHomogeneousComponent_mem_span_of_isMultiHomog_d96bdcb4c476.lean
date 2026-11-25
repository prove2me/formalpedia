-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_weightedHomogeneousComponent_mem_span_of_isMultiHomog_d96bdcb4c476
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:44:51.558372+00:00
-- url     : https://prove2.me/submissions/1a0c42d6-5b61-4cbd-893c-062c138d2e62

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PCutByForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
universe u
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {R : Type*} [CommRing R] {K : Type*}
    [DecidableEq K] {ι : K → Type*} {s : MRing ι R} {c : K → ℕ} (hs : IsMultiHomog s c)
    {t : MRing ι R} (ht : t ∈ Ideal.span {s}) (b : K → ℕ) :
    weightedHomogeneousComponent (blockWeight ι) b t ∈ Ideal.span {s} := by
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp ht
  rw [a.as_sum, Finset.sum_mul, map_sum]
  refine Ideal.sum_mem _ fun d _ => ?_
  have hd : IsWeightedHomogeneous (blockWeight ι) (monomial d (coeff d a) * s)
      (Finsupp.weight (blockWeight ι) d + c) :=
    (isWeightedHomogeneous_monomial _ d _ rfl).mul hs
  by_cases hb : b = Finsupp.weight (blockWeight ι) d + c
  · subst hb
    rw [hd.weightedHomogeneousComponent_same]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
  · rw [hd.weightedHomogeneousComponent_ne b hb]
    exact Ideal.zero_mem _
end GroundTheory.Heights₂.Heights.NumbersDVR
