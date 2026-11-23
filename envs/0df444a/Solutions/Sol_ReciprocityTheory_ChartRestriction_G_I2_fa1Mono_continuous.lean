-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.fa1Mono_continuous
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:42:29.654497+00:00
-- url     : https://prove2.me/submissions/b30ca16b-f8fe-4dbe-99b2-d73a18ea0cd5

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
theorem _root_.solution {g : ℕ} (α : Fin g →₀ ℕ) : Continuous (monomialOfMultiindex α) := by
  have h : monomialOfMultiindex α = fun z : EuclideanSpace ℂ (Fin g) => ∏ i, z i ^ α i := funext (fa1Mono_eq α)
  rw [h]
  exact continuous_finsetProd _ fun i _ => (PiLp.continuous_apply 2 _ i).pow _
end ReciprocityTheory.ChartRestriction.G.I2
