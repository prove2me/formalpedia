-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.Hf_norm_le_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:08:59.886325+00:00
-- url     : https://prove2.me/submissions/ed3e7e90-5228-437b-94f3-7760d8445843

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_CardChoiceLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_HfNormLeTwo
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_I2_Hf_eq_inner__57cc81a446bf


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Complex NumberField
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution {dim : (E →+* ℂ) → ℕ} (e y : Vsp dim) (he : ‖e‖ = 1) (hy : ‖y‖ ≤ 2) :
    ‖Hf e y‖ ≤ 2 := by
  rw [Hf_eq_inner']
  calc ‖inner ℂ y e‖ ≤ ‖y‖ * ‖e‖ := norm_inner_le_norm y e
    _ ≤ 2 := by rw [he, mul_one]; exact hy
end ReciprocityTheory.ChartRestriction.G.I2
