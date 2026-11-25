-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.ChA.Hf_prj_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:54:13.017217+00:00
-- url     : https://prove2.me/submissions/f3092c35-3781-4a73-a114-03c39d31bf51

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_HfRsmulRight
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_ChA_prj_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
noncomputable section
variable {E : Type} [Field E] [NumberField E]
open ReciprocityTheory.ChartRestriction.G.I2.ChA
namespace ReciprocityTheory.ChartRestriction.G.I2.ChA
theorem _root_.solution {dim : (E →+* ℂ) → ℕ} {σ : E →+* ℂ} {v : Vsp dim} (hv : InPart σ v) (x : Vsp dim) :
    Hf v (prj σ x) = Hf v x := by
  unfold Hf
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [prj_apply]
  split_ifs with h
  · rfl
  · rw [hv i h, zero_mul, zero_mul]
end ReciprocityTheory.ChartRestriction.G.I2.ChA
