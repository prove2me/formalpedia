-- Prove2me | solution 1 for QPK.map_inv_eq_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:10:43.934795+00:00
-- url     : https://prove2.me/submissions/3234ec35-55f4-4760-8cf4-ff3c1eeec617

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientHaar_HaarMeasureUniqueness
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientHaar_SiegelMeasureDefinition
import Theorems.Thm_QPK_eq_one_of_eq_mul
import Theorems.Thm_QPK_eq_one_of_mul_self
import Theorems.Thm_QPK_exists_pos_fin
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
    (hμ : InvOn μ K) (hR : ∀ s ∈ K, μ.map (fun x => x * s) = μ) :
    μ.map (fun x => x⁻¹) = μ := by
  obtain ⟨hsf, hne, hKc, hL⟩ := hμ
  have hmeas : Measurable (fun x : G => x⁻¹) := measurable_inv
  have hKm : MeasurableSet K := hc.measurableSet
  have hpre : (fun x : G => x⁻¹) ⁻¹' K = K := by
    ext x
    simp only [Set.mem_preimage]
    constructor
    · intro h
      have h2 := hK.2.2 _ h
      rwa [inv_inv] at h2
    · intro h
      exact hK.2.2 _ h
  have hpreC : (fun x : G => x⁻¹) ⁻¹' Kᶜ = Kᶜ := by
    rw [Set.preimage_compl, hpre]
  have hν : InvOn (μ.map (fun x => x⁻¹)) K := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact (MeasurableEquiv.inv G).sigmaFinite_map
    · exact (Measure.map_ne_zero_iff hmeas.aemeasurable).2 hne
    · rw [Measure.map_apply hmeas hKm.compl, hpreC, hKc]
    · intro t ht
      rw [Measure.map_map (measurable_const_mul t) hmeas]
      have e : (fun x : G => t * x) ∘ (fun x => x⁻¹) = (fun x => x⁻¹) ∘ (fun x => x * t⁻¹) := by
        funext x
        simp [mul_inv_rev]
      rw [e, ← Measure.map_map hmeas (measurable_mul_const t⁻¹), hR t⁻¹ (hK.2.2 t ht)]
  obtain ⟨c, hc0, hct, hceq⟩ := haar_measure_uniqueness G K hc hK _ _ hν ⟨hsf, hne, hKc, hL⟩
  have hinv2 : (μ.map (fun x : G => x⁻¹)).map (fun x => x⁻¹) = μ := by
    rw [Measure.map_map hmeas hmeas]
    have e : (fun x : G => x⁻¹) ∘ (fun x => x⁻¹) = id := by
      funext x
      simp
    rw [e, Measure.map_id]
  have hμc : μ = (c * c) • μ := by
    have h2 := hinv2
    rw [hceq, Measure.map_smul, hceq, smul_smul] at h2
    exact h2.symm
  haveI := hsf
  obtain ⟨A, hA0, hAt⟩ := exists_pos_fin μ hne
  have h3 : μ A = (c * c) * μ A := by
    have h4 := congrArg (fun m : Measure G => m A) hμc
    simpa only [Measure.smul_apply, smul_eq_mul] using h4
  have hcc : c * c = 1 := eq_one_of_eq_mul hA0 hAt h3
  rw [hceq, eq_one_of_mul_self hcc, one_smul]
end QPK
