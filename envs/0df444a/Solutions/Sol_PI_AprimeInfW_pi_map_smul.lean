-- Prove2me | solution 1 for PI.AprimeInfW.pi_map_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:17:46.028076+00:00
-- url     : https://prove2.me/submissions/0d78bc10-e838-4281-ad55-e4600486ebe1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_DetMulRCReal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_PiCoord
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_PlaceAll
import Theorems.Thm_PI_AprimeInfW_pi_smul_measure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.AprimeInfW
open MeasureTheory Matrix
open scoped ENNReal NNReal
namespace PI.AprimeInfW
theorem _root_.solution {V : Type} [Fintype V] {X Y : V → Type} [∀ v, MeasurableSpace (X v)]
    [∀ v, MeasurableSpace (Y v)] (μ : ∀ v, Measure (X v)) (ν : ∀ v, Measure (Y v)) [∀ v, SigmaFinite (ν v)]
    (f : ∀ v, X v → Y v) (hf : ∀ v, Measurable (f v)) (c : V → ℝ≥0)
    (hc : ∀ v, (μ v).map (f v) = c v • ν v) :
    (Measure.pi μ).map (fun x v => f v (x v)) = (∏ v, (c v : ℝ≥0∞)) • Measure.pi ν := by
  haveI : ∀ v, SigmaFinite (μ v) := fun v =>
    SigmaFinite.of_map (μ v) (hf v).aemeasurable (by rw [hc v]; infer_instance)
  rw [← pi_smul_measure]
  symm
  refine Measure.pi_eq fun s hs => ?_
  have hmeas : Measurable (fun x : ∀ v, X v => fun v => f v (x v)) :=
    measurable_pi_lambda _ fun v => (hf v).comp (measurable_pi_apply v)
  rw [Measure.map_apply hmeas (MeasurableSet.univ_pi hs)]
  have hpre : (fun x : ∀ v, X v => fun v => f v (x v)) ⁻¹' Set.univ.pi s =
      Set.univ.pi (fun v => f v ⁻¹' s v) := by
    ext x
    simp
  rw [hpre, Measure.pi_pi]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [← hc v, Measure.map_apply (hf v) (hs v)]
end PI.AprimeInfW
