-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.chartTransport_indicator_memLp_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:41:49.60327+00:00
-- url     : https://prove2.me/submissions/6d7568ca-2468-4526-8655-036d5c7a3d06

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_ChartA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_chT_lint
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_chT_aesm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set Function
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [SecondCountableTopology M] [MeasurableSpace M]
  [BorelSpace M] {n : ℕ} {z : M → V n} {e : OpenPartialHomeomorph M (V n)}
namespace ReciprocityTheory.L2DbarEstimates.F
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [T2Space M] (hz : IsLocalHomeomorph z)
    (he : IsChart n z e) (f : M → E) (hf : LocalL2Isometry (vol n z) f) (hc : HasCompactSupport f)
    (hsub : tsupport f ⊆ e.source) :
    MemLp (e.target.indicator (f ∘ e.symm)) 2 volume := by
  have hae := chT_aesm hz he f hf.1
  refine ⟨hae, ?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  have hz0 : ∀ x, x ∉ tsupport f → f x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  have hs : ∀ x, x ∉ e.source → ‖f x‖ₑ ^ 2 = 0 := by
    intro x hx
    simp [hz0 x (fun h => hx (hsub h))]
  have e1 : ∫⁻ y, ‖e.target.indicator (f ∘ e.symm) y‖ₑ ^ 2 =
      ∫⁻ y in e.target, ‖f (e.symm y)‖ₑ ^ 2 := by
    rw [← lintegral_indicator e.open_target.measurableSet]
    congr 1; funext y
    by_cases hy : y ∈ e.target <;> simp [hy]
  rw [e1, ← chT_lint hz he (fun x => ‖f x‖ₑ ^ 2) (hf.1.enorm.pow_const 2) hs]
  calc ∫⁻ x, ‖f x‖ₑ ^ 2 ∂vol n z = ∫⁻ x in tsupport f, ‖f x‖ₑ ^ 2 ∂vol n z := by
        rw [setLIntegral_eq_of_support_subset]
        intro x hx
        by_contra h
        exact hx (by simp [hz0 x h])
    _ < ⊤ := hf.2 _ hc
end ReciprocityTheory.L2DbarEstimates.F
