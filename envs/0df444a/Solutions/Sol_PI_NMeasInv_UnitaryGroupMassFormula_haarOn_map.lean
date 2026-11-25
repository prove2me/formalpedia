-- Prove2me | solution 1 for PI.NMeasInv.UnitaryGroupMassFormula.haarOn_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:56:45.971134+00:00
-- url     : https://prove2.me/submissions/b368cf56-fdc8-4aff-8974-e651d9e0077d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureInverseContraction_RightInvOfContract

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Measure Topology
open scoped ENNReal NNReal
open PI PI.NMeasInv PI.NMeasInv.UnitaryGroupMassFormula
attribute [local instance] Classical.propDecidable
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
namespace PI.NMeasInv.UnitaryGroupMassFormula
theorem _root_.solution (N : Subgroup G) (hN : IsClosed (N : Set G)) {μ : Measure G} (hμ : HaarOn N μ)
    (φ : G → G) (e : G ≃ₜ G) (he : ⇑e = φ) (hNφ : ∀ x ∈ N, φ x ∈ N)
    (hl : ∀ s ∈ N, ∃ s' ∈ N, ∀ x, s * φ x = φ (s' * x)) : HaarOn N (μ.map φ) := by
  obtain ⟨hσ, h0, hc, hi⟩ := hμ
  have hφm : Measurable φ := by rw [← he]; exact e.measurable
  refine ⟨?_, ?_, ?_, ?_⟩
  · haveI := hσ
    have h1 := e.toMeasurableEquiv.sigmaFinite_map (μ := μ)
    rw [Homeomorph.toMeasurableEquiv_coe, he] at h1
    exact h1
  · exact fun h => h0 ((Measure.map_eq_zero_iff hφm.aemeasurable).mp h)
  · rw [Measure.map_apply hφm hN.isOpen_compl.measurableSet]
    exact measure_mono_null (fun x hx hxN => hx (hNφ x hxN)) hc
  · intro s hs
    obtain ⟨s', hs', hss⟩ := hl s hs
    rw [Measure.map_map (measurable_const_mul s) hφm]
    have h2 : (fun x => s * x) ∘ φ = φ ∘ (fun x => s' * x) := by funext x; exact hss x
    rw [h2, ← Measure.map_map hφm (measurable_const_mul s'), hi s' hs']
end PI.NMeasInv.UnitaryGroupMassFormula
