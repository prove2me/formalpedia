-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ConeMassOfFibre_hypotheses_inhabited_77106a6e7ffc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:39:23.281116+00:00
-- url     : https://prove2.me/submissions/ed201b45-1109-43e3-a616-acb0b31dc34b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeFibre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeMass
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isProjPrime_point_e4b734f59300


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
open MvPolynomial MeasureTheory
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace ConeMassOfFibre
theorem _root_.solution :
    IsProjPrime (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) ∧
      ∀ᵐ π : Fin 1 → Fin 1 → ℂ, ∀ᵐ w : EuclideanSpace ℂ (Fin 1),
        fibreCount (HermNorm.std 1) ⊥ π w = ((1 : ℕ) : ℕ∞) := by
  refine ⟨isProjPrime_point ℂ, ?_⟩
  have hnull : ∀ᵐ π : Fin 1 → Fin 1 → ℂ, π 0 0 ≠ 0 := by
    have hp : MeasurePreserving (fun π : Fin 1 → Fin 1 → ℂ => π 0 0) :=
      (volume_preserving_funUnique (Fin 1) ℂ).comp
        (volume_preserving_funUnique (Fin 1) (Fin 1 → ℂ))
    rw [ae_iff]
    have hset : {π : Fin 1 → Fin 1 → ℂ | ¬ π 0 0 ≠ 0} = (fun π => π 0 0) ⁻¹' {0} := by
      ext π; simp
    rw [hset, hp.measure_preimage (measurableSet_singleton 0).nullMeasurableSet]
    simp
  filter_upwards [hnull] with π hπ
  refine Filter.Eventually.of_forall fun w => ?_
  have hfib : {y | y ∈ coneSet (HermNorm.std 1) ⊥ ∧ linProj π y = w} =
      {WithLp.toLp 2 fun _ => w 0 / π 0 0} := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, coneSet, Ideal.mem_bot]
    constructor
    · rintro ⟨-, hy⟩
      have h0 := congrArg (fun v : EuclideanSpace ℂ (Fin 1) => v 0) hy
      simp only [linProj, Fin.sum_univ_one] at h0
      ext i
      fin_cases i
      simp only [Fin.zero_eta, Fin.isValue]
      rw [← h0]
      field_simp
    · rintro rfl
      refine ⟨fun q hq => by simp [hq], ?_⟩
      ext i
      fin_cases i
      simp [linProj]
      field_simp
  rw [fibreCount, hfib, Set.encard_singleton]
  rfl
end ConeMassOfFibre
end GroundTheory.Heights₂.Heights
