-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.regM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:23:34.031617+00:00
-- url     : https://prove2.me/submissions/d808c8ce-5ee7-4a3a-900c-3e2073d3c190

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_HoloWeakStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_RegGlue
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_HormanderEstimate_RegMDbEqZeroOfNotMem
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_regM_of_measurable
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_db
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mono


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M]
namespace ReciprocityTheory.L2DbarEstimates.F
theorem _root_.solution (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (hReg : C.RegStatement) (hExt : ExtendStatement n M) : RegMStatement n M := by
  intro z hz F hF hw
  obtain ⟨hFae, hF2⟩ := hF
  have hFF' : F =ᵐ[vol n z] hFae.mk F := hFae.ae_eq_mk
  have hF'm : Measurable (hFae.mk F) := hFae.stronglyMeasurable_mk.measurable
  have hF'L : LocalL2Isometry (vol n z) (hFae.mk F) := by
    refine ⟨hFae.stronglyMeasurable_mk.aestronglyMeasurable, fun C hC => ?_⟩
    calc ∫⁻ x in C, ‖hFae.mk F x‖ₑ ^ 2 ∂vol n z = ∫⁻ x in C, ‖F x‖ₑ ^ 2 ∂vol n z :=
          lintegral_congr_ae (ae_restrict_of_ae (hFF'.mono fun x hx => by simp only [hx]))
      _ < ⊤ := hF2 C hC
  have hw' : ∀ φ : M → ℂ, IsTest n z φ → ∀ j : Fin n,
      ∫ x, hFae.mk F x * db n z j φ x ∂vol n z = 0 := by
    intro φ hφ j
    rw [← hw φ hφ j]
    exact integral_congr_ae (hFF'.mono fun x hx => by simp only [hx])
  obtain ⟨G, hG, hG'⟩ := regM_of_measurable hReg hExt z hz (hFae.mk F) hF'm hF'L hw'
  exact ⟨G, hG, hFF'.trans hG'⟩
end ReciprocityTheory.L2DbarEstimates.F
