-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.FPw.ka_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:08:35.309443+00:00
-- url     : https://prove2.me/submissions/e990a0ae-6505-49e2-a6e8-302f9ac826a2

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_PaUContinuous
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaSA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_HfNegRight

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
theorem _root_.solution {Y : GT ι} {q : ℕ} (hC : Coc Y q) : Y.ka 0 = 1 := by
  have h := hC 0 (Submodule.zero_mem _) 0 (Submodule.zero_mem _)
  have hz : Hf (0 : EuclideanSpace ℂ ι) 0 = 0 := by simp [Hf]
  simp only [add_zero, hz, Complex.zero_im, mul_zero, neg_zero, Complex.ofReal_zero, zero_mul,
    Complex.exp_zero, mul_one] at h
  have hne : Y.ka 0 ≠ 0 := by
    intro h0
    have h1 := Y.ka_abs 0 (Submodule.zero_mem _)
    rw [h0, norm_zero] at h1
    exact zero_ne_one h1
  exact mul_left_cancel₀ hne (h.symm.trans (mul_one _).symm)
end ReciprocityTheory.ChartRestriction.G.I2.FPw
