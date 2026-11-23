-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.FPw.paU_norm_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:56:33.050645+00:00
-- url     : https://prove2.me/submissions/40b8c7e1-d867-4304-a954-dcc0ea483cc0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_HfEqInner
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_PaUContinuous
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_FPw_Hf_eq_inner


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.FPw
open MeasureTheory Complex
noncomputable section
variable {ι : Type} [Fintype ι]
open Classical
namespace ReciprocityTheory.ChartRestriction.G.I2.FPw
theorem _root_.solution (q : ℕ) (a v : EuclideanSpace ℂ ι) (F : EuclideanSpace ℂ ι → ℂ) :
    ‖paU q a F v‖ * paW q v = ‖F (v - a)‖ * (Real.exp (-(q * Real.pi) * ‖v - (1 / 2 : ℂ) • a‖ ^ 2) *
      Real.exp (-(q * Real.pi) * ‖a‖ ^ 2 / 4)) := by
  have hre : (q * Real.pi * Hf v a - q * Real.pi * Hf a a / 2 : ℂ).re =
      q * Real.pi * RCLike.re (inner ℂ a v) - q * Real.pi * ‖a‖ ^ 2 / 2 := by
    rw [Hf_eq_inner, Hf_eq_inner, inner_self_eq_norm_sq_to_K]
    simp [Complex.mul_re]
    left
    rw [← Complex.ofReal_pow]
    exact Complex.ofReal_re _
  have hsq : ‖v - (1 / 2 : ℂ) • a‖ ^ 2 = ‖v‖ ^ 2 - RCLike.re (inner ℂ a v) + ‖a‖ ^ 2 / 4 := by
    rw [@norm_sub_sq ℂ, inner_smul_right, norm_smul]
    simp
    rw [← inner_conj_symm v a, Complex.conj_re]
    ring
  unfold paU paW
  rw [norm_mul, Complex.norm_exp, hre, hsq, mul_comm (Real.exp _) ‖F (v - a)‖, mul_assoc,
    ← Real.exp_add, ← Real.exp_add]
  congr 2
  ring
end ReciprocityTheory.ChartRestriction.G.I2.FPw
