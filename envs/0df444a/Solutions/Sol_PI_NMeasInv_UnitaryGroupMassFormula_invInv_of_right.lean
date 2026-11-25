-- Prove2me | solution 1 for PI.NMeasInv.UnitaryGroupMassFormula.invInv_of_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:15:09.648305+00:00
-- url     : https://prove2.me/submissions/9a675633-f64a-4906-91bd-50ed912c8a0a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureInverseContraction_RightInvOfContract
import Theorems.Thm_PI_NMeasInv_UnitaryGroupMassFormula_haarOn_unique
import Theorems.Thm_PI_NMeasInv_UnitaryGroupMassFormula_exists_K
import Theorems.Thm_PI_NMeasInv_UnitaryGroupMassFormula_smul_cancel

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
    (hR : ∀ n ∈ N, μ.map (fun x => x * n) = μ) : μ.map (fun x => x⁻¹) = μ := by
  have hinv : HaarOn N (μ.map (fun x => x⁻¹)) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · haveI := hμ.1
      have h1 := (Homeomorph.inv G).toMeasurableEquiv.sigmaFinite_map (μ := μ)
      simpa using h1
    · intro h; exact hμ.2.1 ((Measure.map_eq_zero_iff measurable_inv.aemeasurable).mp h)
    · rw [Measure.map_apply measurable_inv hN.isOpen_compl.measurableSet]
      exact measure_mono_null (show (fun x : G => x⁻¹) ⁻¹' (N : Set G)ᶜ ⊆ (N : Set G)ᶜ from
        fun x hx hxN => hx (N.inv_mem hxN)) hμ.2.2.1
    · intro s hs
      rw [Measure.map_map (measurable_const_mul s) measurable_inv]
      have h2 : (fun x => s * x) ∘ (fun x : G => x⁻¹) = (fun x : G => x⁻¹) ∘ (fun x => x * s⁻¹) := by
        funext x; simp [mul_inv_rev]
      rw [h2, ← Measure.map_map measurable_inv (measurable_mul_const s⁻¹), hR s⁻¹ (N.inv_mem hs)]
  obtain ⟨c, hc0, hct, hcμ⟩ := haarOn_unique N hN hμ hinv
  have hii : (μ.map (fun x : G => x⁻¹)).map (fun x : G => x⁻¹) = μ := by
    rw [Measure.map_map measurable_inv measurable_inv]
    have h3 : ((fun x : G => x⁻¹) ∘ fun x : G => x⁻¹) = id := by funext x; simp
    rw [h3, Measure.map_id]
  have hcc : (c * c) • μ = (1 : ℝ≥0∞) • μ := by
    rw [one_smul, mul_smul]
    conv_rhs => rw [← hii, hcμ, Measure.map_smul, hcμ]
  obtain ⟨K, hK, hK0, hKt⟩ := exists_K N hN μ hμ
  have h1 : c * c = 1 := smul_cancel hK0 hKt hcc
  have h2 : c = 1 := by
    rcases lt_trichotomy c 1 with h | h | h
    · exfalso
      have h4 : c * c < 1 * 1 := ENNReal.mul_lt_mul h h
      simp [h1] at h4
    · exact h
    · exfalso
      have h4 : 1 * 1 < c * c := ENNReal.mul_lt_mul h h
      simp [h1] at h4
  rw [hcμ, h2, one_smul]
end PI.NMeasInv.UnitaryGroupMassFormula
