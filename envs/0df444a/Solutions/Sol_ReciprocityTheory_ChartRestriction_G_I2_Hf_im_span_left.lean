-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.Hf_im_span_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:01:55.326806+00:00
-- url     : https://prove2.me/submissions/bfeb5895-eee7-4bdb-b17f-4fb34fc7ebbf

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_Hf_im_add_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_Hf_im_smul_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_Hf_im_zero_left

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
open scoped InnerProductSpace
noncomputable section
variable {ι : Type} [Fintype ι]
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution (S : Set (EuclideanSpace ℂ ι)) (w : EuclideanSpace ℂ ι)
    (h : ∀ v ∈ S, (Hf v w).im = 0) : ∀ v ∈ Submodule.span ℝ S, (Hf v w).im = 0 := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => exact Hf_im_zero_left w
  | add x y _ _ hx hy => rw [Hf_im_add_left, hx, hy, add_zero]
  | smul a x _ hx => rw [Hf_im_smul_left, hx, mul_zero]
end ReciprocityTheory.ChartRestriction.G.I2
