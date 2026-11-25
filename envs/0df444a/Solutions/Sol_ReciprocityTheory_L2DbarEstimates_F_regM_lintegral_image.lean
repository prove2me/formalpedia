-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.regM_lintegral_image
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:42:42.095521+00:00
-- url     : https://prove2.me/submissions/53952b69-08e4-44d2-b601-8f857520a3fd

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_HoloWeakStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_RegGlue
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_HormanderEstimate_RegMDbEqZeroOfNotMem
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mono
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_lintegral_vol_chart


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
    (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) (f : M → ℝ≥0∞) (hf : Measurable f)
    (K : Set (V n)) (hK : IsCompact K) (hKt : K ⊆ e.target) :
    ∫⁻ y in K, f (e.symm y) = ∫⁻ x in e.symm '' K, f x ∂vol n z := by
  have hC : IsCompact (e.symm '' K) := hK.image_of_continuousOn (e.continuousOn_symm.mono hKt)
  have hCm : MeasurableSet (e.symm '' K) := hC.isClosed.measurableSet
  have hCs : e.symm '' K ⊆ e.source := by
    rintro _ ⟨y, hy, rfl⟩; exact e.map_target (hKt hy)
  rw [← lintegral_indicator hCm, lintegral_vol_chart n z hz e he _ (hf.indicator hCm)
    (fun x hx => indicator_of_notMem (fun h => hx (hCs h)) _)]
  have h1 : ∫⁻ y in K, f (e.symm y) = ∫⁻ y in e.target, K.indicator (fun y => f (e.symm y)) y := by
    rw [lintegral_indicator hK.measurableSet, Measure.restrict_restrict hK.measurableSet,
      inter_eq_self_of_subset_left hKt]
  rw [h1]
  refine setLIntegral_congr_fun e.open_target.measurableSet (fun y hy => ?_)
  by_cases hyK : y ∈ K
  · rw [indicator_of_mem hyK, indicator_of_mem (mem_image_of_mem _ hyK)]
  · rw [indicator_of_notMem hyK, indicator_of_notMem]
    rintro ⟨k, hk, hke⟩
    have : k = y := e.symm.injOn (by simpa using hKt hk) (by simpa using hy) hke
    exact hyK (this ▸ hk)
end ReciprocityTheory.L2DbarEstimates.F
