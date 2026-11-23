-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.Col.inner_uc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:20:29.201939+00:00
-- url     : https://prove2.me/submissions/e5d8edd2-760e-4304-b49c-aa7a82414db7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SecondProjectionOrthogonalComplement
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_Col_Hf_rsmul_r
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_Col_Hf_sum_r

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open Complex
open scoped InnerProductSpace
noncomputable section
open ReciprocityTheory.ChartRestriction.G.I2.Col
variable {ι : Type} [Fintype ι]
variable (K : Submodule ℝ (EuclideanSpace ℂ ι))
namespace ReciprocityTheory.ChartRestriction.G.I2.Col
theorem _root_.solution (v : EuclideanSpace ℂ ι) (a : EuclideanSpace ℂ ι) (ha : a ∈ K) :
    ⟪uc K v, a⟫_ℝ = (Hf v a).im := by
  have ha' : ∑ k, ⟪e K k, a⟫_ℝ • e K k = a := by
    have h2 := congrArg (fun x : K => (x : EuclideanSpace ℂ ι)) ((ob K).sum_repr' ⟨a, ha⟩)
    simpa only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_inner, e] using h2
  conv_rhs => rw [← ha']
  rw [Hf_sum_r, Complex.im_sum, uc, sum_inner]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Hf_rsmul_r, Complex.im_ofReal_mul, real_inner_smul_left, z, mul_comm]
end ReciprocityTheory.ChartRestriction.G.I2.Col
