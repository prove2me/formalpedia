-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_aeval_weightedHomogeneousComponent_of_forms_5c48238267f9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:40:43.193438+00:00
-- url     : https://prove2.me/submissions/5204f810-c908-42b2-9fa5-ac5863467405

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_CutIdentityRightSideCongrOfSubMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsReesAlgebraDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PBlowUpModel

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
variable {σ : Type*} {R : Type*} [CommRing R]
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {K : Type*} [DecidableEq K] {ι : K → Type*}
    (ω : σ → K → ℕ) (e : σ → MRing ι R) (he : ∀ v, IsMultiHomog (e v) (ω v)) (m : K → ℕ)
    (p : MvPolynomial σ R) :
    aeval e (weightedHomogeneousComponent ω m p) =
      weightedHomogeneousComponent (blockWeight ι) m (aeval e p) := by
  induction p using MvPolynomial.induction_on' with
  | monomial d c =>
    have hmon : IsWeightedHomogeneous (blockWeight ι) (aeval e (monomial d c))
        (Finsupp.weight ω d) := by
      rw [aeval_monomial, Finsupp.weight_apply, algebraMap_eq]
      have := (isWeightedHomogeneous_C (blockWeight ι) c).mul (IsWeightedHomogeneous.prod d.support
        (fun v => e v ^ d v) (fun v => d v • ω v) (fun v _ => (he v).pow (d v)))
      rw [zero_add] at this
      exact this
    by_cases hdm : Finsupp.weight ω d = m
    · have hmon' : IsWeightedHomogeneous (blockWeight ι) (aeval e (monomial d c)) m := hdm ▸ hmon
      rw [(isWeightedHomogeneous_monomial _ d c hdm).weightedHomogeneousComponent_same,
        hmon'.weightedHomogeneousComponent_same]
    · rw [(isWeightedHomogeneous_monomial ω d c
        (m := Finsupp.weight ω d) rfl).weightedHomogeneousComponent_ne m
        (Ne.symm hdm), hmon.weightedHomogeneousComponent_ne m (Ne.symm hdm), map_zero]
  | add p q hp hq => simp only [map_add, hp, hq]
end GroundTheory.Heights₂.Heights.NumbersDVR
