-- Prove2me | solution 1 for PI.AprimeInfG.measurePreserving_piCurry_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:19:14.887819+00:00
-- url     : https://prove2.me/submissions/e3ce4de6-41ea-4eb1-ac8f-37519d7c7cde

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
theorem _root_.solution {V : Type} [Fintype V] {α : V → Type} [∀ v, Fintype (α v)]
    {X : ∀ v, α v → Type} [∀ v a, MeasurableSpace (X v a)] (μ : ∀ v a, Measure (X v a))
    [∀ v a, SigmaFinite (μ v a)] :
    MeasurePreserving (MeasurableEquiv.piCurry X).symm (Measure.pi fun v => Measure.pi fun a => μ v a)
      (Measure.pi fun p : Σ v, α v => μ p.1 p.2) := by
  refine ⟨(MeasurableEquiv.piCurry X).symm.measurable, ?_⟩
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply (MeasurableEquiv.piCurry X).symm.measurable (MeasurableSet.univ_pi hs)]
  have e : (MeasurableEquiv.piCurry X).symm ⁻¹' Set.univ.pi s =
      Set.univ.pi fun v => Set.univ.pi fun a => s ⟨v, a⟩ := by
    ext z
    simp only [Set.mem_preimage, Set.mem_univ_pi, Sigma.forall, MeasurableEquiv.coe_piCurry_symm]
    exact Iff.rfl
  rw [e, Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  rw [Fintype.prod_sigma]
end PI.AprimeInfG
