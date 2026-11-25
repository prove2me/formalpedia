-- Prove2me | solution 1 for PI.AprimeInfG.measurePreserving_piProdEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:09:56.620803+00:00
-- url     : https://prove2.me/submissions/c7a44180-8b62-46c0-a076-f501f994da49

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_PiCoord

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
theorem _root_.solution {V : Type} [Fintype V] (A B : V → Type) [∀ v, MeasurableSpace (A v)]
    [∀ v, MeasurableSpace (B v)] (μ : ∀ v, Measure (A v)) (ν : ∀ v, Measure (B v)) [∀ v, SigmaFinite (μ v)]
    [∀ v, SigmaFinite (ν v)] :
    MeasurePreserving (piProdEquiv A B) (Measure.pi fun v => (μ v).prod (ν v))
      ((Measure.pi fun v => μ v).prod (Measure.pi fun v => ν v)) where
  measurable := (piProdEquiv A B).measurable
  map_eq := by
    refine (Measure.FiniteSpanningSetsIn.ext ?_ (isPiSystem_pi.prod isPiSystem_pi)
      ((Measure.FiniteSpanningSetsIn.pi fun i ↦ (μ i).toFiniteSpanningSetsIn).prod
      (Measure.FiniteSpanningSetsIn.pi (fun i ↦ (ν i).toFiniteSpanningSetsIn))) ?_).symm
    · refine (generateFrom_eq_prod generateFrom_pi generateFrom_pi ?_ ?_).symm
      · exact (Measure.FiniteSpanningSetsIn.pi (fun i ↦ (μ i).toFiniteSpanningSetsIn)).isCountablySpanning
      · exact (Measure.FiniteSpanningSetsIn.pi (fun i ↦ (ν i).toFiniteSpanningSetsIn)).isCountablySpanning
    · rintro _ ⟨s, ⟨s, _, rfl⟩, ⟨_, ⟨t, _, rfl⟩, rfl⟩⟩
      rw [MeasurableEquiv.map_apply]
      rw [show (piProdEquiv A B) ⁻¹' (Set.univ.pi s ×ˢ Set.univ.pi t) =
          (Set.univ.pi fun i ↦ s i ×ˢ t i) by
          ext; simp [Set.mem_pi, forall_and, piProdEquiv]]
      simp_rw [Measure.pi_pi, Measure.prod_prod, Measure.pi_pi, Finset.prod_mul_distrib]
end PI.AprimeInfG
