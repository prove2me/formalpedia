-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.regM_locInt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:02:18.888445+00:00
-- url     : https://prove2.me/submissions/8eef68b2-6ae8-4c9b-8fdd-d9bc6185bdba

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_HoloWeakStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_RegGlue
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_HormanderEstimate_RegMDbEqZeroOfNotMem
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_regM_lintegral_image
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mono
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_integrable


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
theorem _root_.solution {n : ℕ} (z : M → V n) (hz : IsLocalHomeomorph z)
    (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) (F : M → ℂ) (hFm : Measurable F)
    (hF : LocalL2Isometry (vol n z) F) : LocallyIntegrableOn (F ∘ e.symm) e.target volume := by
  rw [locallyIntegrableOn_iff e.open_target.isLocallyClosed]
  intro K hKt hK
  have hcont : ContinuousOn e.symm K := e.continuousOn_symm.mono hKt
  have hmeas : AEStronglyMeasurable (F ∘ e.symm) (volume.restrict K) :=
    (hFm.comp_aemeasurable (hcont.aemeasurable hK.measurableSet)).aestronglyMeasurable
  have h2 : ∫⁻ y in K, ‖(F ∘ e.symm) y‖ₑ ^ 2 < ⊤ := by
    have h3 := regM_lintegral_image z hz e he (fun x => ‖F x‖ₑ ^ 2) (hFm.enorm.pow_const 2) K hK hKt
    simp only [Function.comp_apply]
    rw [h3]
    exact hF.2 _ (hK.image_of_continuousOn hcont)
  haveI : IsFiniteMeasure (volume.restrict K) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
  have hL2 : MemLp (F ∘ e.symm) 2 (volume.restrict K) := by
    refine ⟨hmeas, ?_⟩
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top]
    simpa [ENNReal.rpow_two] using h2
  exact hL2.integrable one_le_two
end ReciprocityTheory.L2DbarEstimates.F
