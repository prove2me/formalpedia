-- Prove2me | solution 1 for PI.AprimeInfG.withDensity_pi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:35:21.355365+00:00
-- url     : https://prove2.me/submissions/7f907f59-2a15-46af-bdfb-f04cd91a2738

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_PiDens
import Theorems.Thm_PI_AprimeInfG_lintegral_fintype_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.AprimeInfG
open MeasureTheory Set
open scoped ENNReal
namespace PI.AprimeInfG
theorem _root_.solution {ι : Type} [Fintype ι] {E : ι → Type} [∀ i, MeasurableSpace (E i)]
    (lam : (i : ι) → Measure (E i)) [∀ i, SigmaFinite (lam i)] (D : (i : ι) → E i → ℝ)
    (hD : ∀ i, Measurable (D i)) :
    (Measure.pi lam).withDensity (fun z => ∏ i, ENNReal.ofReal (D i (z i))) =
      Measure.pi (fun i => (lam i).withDensity (fun x => ENNReal.ofReal (D i x))) := by
  classical
  haveI : ∀ i, SigmaFinite ((lam i).withDensity fun x => ENNReal.ofReal (D i x)) :=
    fun i => SigmaFinite.withDensity_ofReal (D i)
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), ← lintegral_indicator (MeasurableSet.univ_pi hs)]
  have h1 : (univ.pi s).indicator (fun z : (i : ι) → E i => ∏ i, ENNReal.ofReal (D i (z i))) =
      fun z => ∏ i, (s i).indicator (fun x => ENNReal.ofReal (D i x)) (z i) := by
    funext z
    by_cases hz : z ∈ univ.pi s
    · rw [indicator_of_mem hz]
      exact Finset.prod_congr rfl fun i _ => (indicator_of_mem (hz i (mem_univ i)) (fun x => ENNReal.ofReal (D i x))).symm
    · simp only [Set.mem_pi, mem_univ, true_implies, not_forall] at hz
      obtain ⟨i, hi⟩ := hz
      have hz' : z ∉ univ.pi s := fun h => hi (h i (mem_univ i))
      rw [indicator_apply, if_neg hz']
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (by rw [indicator_apply, if_neg hi])).symm
  rw [h1, lintegral_fintype_prod (fun i => (s i).indicator (fun x => ENNReal.ofReal (D i x))) (fun i => (ENNReal.measurable_ofReal.comp (hD i)).indicator (hs i))]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [withDensity_apply _ (hs i), lintegral_indicator (hs i)]
end PI.AprimeInfG
