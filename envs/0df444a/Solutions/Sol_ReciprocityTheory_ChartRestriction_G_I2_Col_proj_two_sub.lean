-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.Col.proj_two_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:14:03.839346+00:00
-- url     : https://prove2.me/submissions/d71986be-9323-4adc-93eb-c25b29ca57d1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SecondProjectionOrthogonalComplement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_MemOfProjTwoEqZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_Col_Hf_sub_l


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open Complex NumberField
open scoped InnerProductSpace
noncomputable section
open ReciprocityTheory.ChartRestriction.G.I2.Col
variable {E : Type} [Field E] [NumberField E]
variable (X : PT E) (I : Submodule ℤ (Vsp X.dim))
variable {X I}
namespace ReciprocityTheory.ChartRestriction.G.I2.Col
theorem _root_.solution (K : Submodule ℝ (Vsp X.dim)) (x y : Vsp X.dim) : p2 K (x - y) = p2 K x - p2 K y := by
  simp only [p2, p1, z, Hf_sub_l, sub_smul, Finset.sum_sub_distrib]; abel
end ReciprocityTheory.ChartRestriction.G.I2.Col
