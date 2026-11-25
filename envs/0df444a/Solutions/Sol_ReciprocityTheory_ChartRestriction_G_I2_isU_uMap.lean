-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.isU_uMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:24:13.16669+00:00
-- url     : https://prove2.me/submissions/bcd04c98-c2dc-4fd8-b3d6-1a41fd581bbc

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SupRatioLeOfPhaseZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TofSpanCondition
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_tof_re_inner_negI
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_dim


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
noncomputable section
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution {dim : (E →+* ℂ) → ℕ} (I : Submodule ℤ (Vsp dim)) (x : Vsp dim) :
    IsU I x (uMap I x) := by
  refine ⟨(IR I).starProjection_apply_mem _, fun a ha => ?_⟩
  show inner ℝ ((IR I).starProjection ((-Complex.I) • x)) a = (Hf x a).im
  have h0 := Submodule.starProjection_inner_eq_zero (K := IR I) ((-Complex.I) • x) a ha
  rw [inner_sub_left, sub_eq_zero] at h0
  rw [← h0, real_inner_comm]
  exact tof_re_inner_negI a x
end ReciprocityTheory.ChartRestriction.G.I2
