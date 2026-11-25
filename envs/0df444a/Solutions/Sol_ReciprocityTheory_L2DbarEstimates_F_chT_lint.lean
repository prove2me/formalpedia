-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.chT_lint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:22:29.064924+00:00
-- url     : https://prove2.me/submissions/2cb945e0-ad98-49c3-ab02-937831fb1492

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_ChartA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_chT_aem_symm
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_vol_restrict_source


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
theorem _root_.solution (hz : IsLocalHomeomorph z) (he : IsChart n z e) (f : M → ℝ≥0∞)
    (hf : AEMeasurable f (vol n z)) (hs : ∀ x, x ∉ e.source → f x = 0) :
    ∫⁻ x, f x ∂vol n z = ∫⁻ y in e.target, f (e.symm y) := by
  have hsub : Function.support f ⊆ e.source := fun x hx => by
    by_contra h; exact hx (hs x h)
  rw [← setLIntegral_eq_of_support_subset hsub, vol_restrict_source n z hz e he]
  have hf' : AEMeasurable f (Measure.map e.symm (volume.restrict e.target)) := by
    rw [← vol_restrict_source n z hz e he]; exact hf.restrict
  exact lintegral_map' hf' (chT_aem_symm (e := e))
end ReciprocityTheory.L2DbarEstimates.F
