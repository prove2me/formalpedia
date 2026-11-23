-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.ae_coord_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:54:25.339065+00:00
-- url     : https://prove2.me/submissions/0b3d3310-407f-4eca-820c-59c8a8ad8c20

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenOfPoincareLelongHyperplane
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_HessCRestrictThm
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContDiffOfContDiffOnZeroOff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution {n : ℕ} (i : Fin (n + 1)) : ∀ᵐ z : Fin (n + 1) → ℂ ∂volume, z i ≠ 0 := by
  rw [ae_iff]
  simp only [ne_eq, not_not]
  rw [volume_pi]
  exact Measure.pi_hyperplane _ i 0
end ReciprocityTheory.AnForm.A
