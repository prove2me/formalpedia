-- Prove2me | solution 1 for QPK.map_mul_right_eq_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:04:51.398536+00:00
-- url     : https://prove2.me/submissions/ae42a0ec-1d2a-48c9-944b-bdae540199a8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientHaar_HaarMeasureUniqueness
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientHaar_SiegelMeasureDefinition
import Theorems.Thm_QPK_eq_one_of_eq_mul
import Theorems.Thm_QPK_haar_measure_uniqueness


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Measure Topology Set
open scoped ENNReal Pointwise
open QPK
variable {G : Type} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
namespace QPK
theorem _root_.solution (K : Set G) (hc : IsClosed K) (hK : IsGrp K) (μ : Measure G)
    (hμ : InvOn μ K) (hfin : μ K ≠ ⊤) (s : G) (hs : s ∈ K) :
    μ.map (fun x => x * s) = μ := by
  obtain ⟨hsf, hne, hKc, hL⟩ := hμ
  have hmeas : Measurable (fun x : G => x * s) := measurable_mul_const s
  have hKm : MeasurableSet K := hc.measurableSet
  have hpre : (fun x : G => x * s) ⁻¹' K = K := by
    ext x
    simp only [Set.mem_preimage]
    constructor
    · intro h
      have h2 := hK.2.1 _ h _ (hK.2.2 s hs)
      rwa [mul_assoc, mul_inv_cancel, mul_one] at h2
    · intro h
      exact hK.2.1 _ h _ hs
  have hpreC : (fun x : G => x * s) ⁻¹' Kᶜ = Kᶜ := by
    rw [Set.preimage_compl, hpre]
  have hν : InvOn (μ.map (fun x => x * s)) K := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact (MeasurableEquiv.mulRight s).sigmaFinite_map
    · exact (Measure.map_ne_zero_iff hmeas.aemeasurable).2 hne
    · rw [Measure.map_apply hmeas hKm.compl, hpreC, hKc]
    · intro t ht
      rw [Measure.map_map (measurable_const_mul t) hmeas]
      have e : (fun x : G => t * x) ∘ (fun x => x * s) = (fun x => x * s) ∘ (fun x => t * x) := by
        funext x
        simp [mul_assoc]
      rw [e, ← Measure.map_map hmeas (measurable_const_mul t), hL t ht]
  obtain ⟨c, hc0, hct, hceq⟩ := haar_measure_uniqueness G K hc hK _ _ hν ⟨hsf, hne, hKc, hL⟩
  have hμK : μ K ≠ 0 := by
    intro h0
    apply hne
    rw [← Measure.measure_univ_eq_zero, ← Set.union_compl_self K]
    exact measure_union_null h0 hKc
  have h1 : μ K = c * μ K := by
    have h2 := congrArg (fun m : Measure G => m K) hceq
    simp only [Measure.smul_apply, smul_eq_mul] at h2
    rwa [Measure.map_apply hmeas hKm, hpre] at h2
  have hc1 : c = 1 := eq_one_of_eq_mul hμK hfin h1
  rw [hceq, hc1, one_smul]
end QPK
