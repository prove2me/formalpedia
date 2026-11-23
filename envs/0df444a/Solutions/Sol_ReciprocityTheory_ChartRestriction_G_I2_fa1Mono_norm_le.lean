-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.fa1Mono_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:58:03.09271+00:00
-- url     : https://prove2.me/submissions/126fbab0-15b4-4f27-93d5-45d5200e3029

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_IntegrableNormPowMulExpNegMulNormSq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_fa1Mono_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution {g : ℕ} (α : Fin g →₀ ℕ) (z : EuclideanSpace ℂ (Fin g)) :
    ‖monomialOfMultiindex α z‖ ≤ ‖z‖ ^ (∑ i, α i) := by
  rw [fa1Mono_eq, norm_prod, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i _ => ?_
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (PiLp.norm_apply_le z i) _
end ReciprocityTheory.ChartRestriction.G.I2
