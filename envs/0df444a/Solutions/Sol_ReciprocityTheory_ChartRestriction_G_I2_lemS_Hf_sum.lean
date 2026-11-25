-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.lemS_Hf_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:15:26.628883+00:00
-- url     : https://prove2.me/submissions/294c02fa-e3bf-4d82-b804-26946d5a46d3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaSA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_lemS_Hf_im

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Complex
open scoped Matrix
noncomputable section
variable {ι : Type} [Fintype ι]
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution {n : ℕ} (c : Fin n → ℤ) (v : Fin n → EuclideanSpace ℂ ι) (y : EuclideanSpace ℂ ι) :
    (Hf (∑ i, c i • v i) y).im = ∑ i, (c i : ℝ) * (Hf (v i) y).im := by
  rw [lemS_Hf_im]
  simp only [lemS_Hf_im, Finset.smul_sum, inner_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_comm, ← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_right]
end ReciprocityTheory.ChartRestriction.G.I2
