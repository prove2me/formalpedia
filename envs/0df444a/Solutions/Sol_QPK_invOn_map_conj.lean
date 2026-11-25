-- Prove2me | solution 1 for QPK.invOn_map_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:04:44.6376+00:00
-- url     : https://prove2.me/submissions/f5eb8b66-fb62-4479-9e23-98d4d5212297

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientHaar_HaarMeasureUniqueness
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientHaar_ConjugationInvariantMeasure
import Theorems.Thm_QPK_measurable_conj
import Theorems.Thm_QPK_conj_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Topology
open scoped ENNReal
open QPK
variable {G : Type} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
namespace QPK
theorem _root_.solution {N : Set G} (hNc : IsClosed N) (h : G)
    (hn1 : ∀ m ∈ N, h * m * h⁻¹ ∈ N) (hn2 : ∀ m ∈ N, h⁻¹ * m * h⁻¹⁻¹ ∈ N)
    {μ : Measure G} (hμ : InvOn μ N) : InvOn (μ.map (fun x => h * x * h⁻¹)) N := by
  obtain ⟨hsf, hne, hc, hinv⟩ := hμ
  haveI := hsf
  have hm : Measurable (fun x : G => h * x * h⁻¹) := measurable_conj h
  have hm' : Measurable (fun x : G => h⁻¹ * x * h⁻¹⁻¹) := measurable_conj h⁻¹
  have hid : (fun x : G => h⁻¹ * x * h⁻¹⁻¹) ∘ (fun x : G => h * x * h⁻¹) = id := by
    rw [conj_comp]
    funext x
    simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h1 : SigmaFinite ((μ.map (fun x : G => h * x * h⁻¹)).map (fun x : G => h⁻¹ * x * h⁻¹⁻¹)) := by
      rw [Measure.map_map hm' hm, hid, Measure.map_id]
      exact hsf
    exact SigmaFinite.of_map _ hm'.aemeasurable h1
  · exact (Measure.map_ne_zero_iff hm.aemeasurable).mpr hne
  · rw [Measure.map_apply hm hNc.measurableSet.compl]
    refine measure_mono_null ?_ hc
    intro x hx hxN
    exact hx (hn1 x hxN)
  · intro s hs
    have hs' : h⁻¹ * s * h⁻¹⁻¹ ∈ N := hn2 s hs
    have hms : Measurable (fun x : G => s * x) := measurable_const_mul s
    have hms' : Measurable (fun x : G => (h⁻¹ * s * h⁻¹⁻¹) * x) := measurable_const_mul _
    rw [Measure.map_map hms hm]
    have e : (fun x : G => s * x) ∘ (fun x : G => h * x * h⁻¹) =
        (fun x : G => h * x * h⁻¹) ∘ (fun x : G => (h⁻¹ * s * h⁻¹⁻¹) * x) := by
      funext x
      simp only [Function.comp_apply, inv_inv]
      group
    rw [e, ← Measure.map_map hm hms', hinv _ hs']
end QPK
