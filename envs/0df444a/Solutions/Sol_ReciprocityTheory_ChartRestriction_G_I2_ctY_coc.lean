-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.ctY_coc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:10:36.53601+00:00
-- url     : https://prove2.me/submissions/0c0a32d0-82b7-496f-9b06-12df41841be9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SecondProjectionOrthogonalComplement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropASt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ColTorusC
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_Col_Hf_add_l


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
noncomputable section
variable {ι : Type} [Fintype ι]
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution (Y : GT ι) (w : EuclideanSpace ℂ ι) (q : ℕ) (h : Y.Coc q) : (ctY Y w).Coc q := by
  intro γ hγ γ' hγ'
  show Y.ka (γ + γ') * cexp (2 * Real.pi * (Hf (γ + γ') w).im * I) =
    Y.ka γ * cexp (2 * Real.pi * (Hf γ w).im * I) * (Y.ka γ' * cexp (2 * Real.pi * (Hf γ' w).im * I)) *
      cexp (-(Real.pi * q * (Hf γ γ').im) * I)
  rw [h γ hγ γ' hγ', Col.Hf_add_l, Complex.add_im]
  have e : cexp (2 * Real.pi * (((Hf γ w).im + (Hf γ' w).im : ℝ) : ℂ) * I) =
      cexp (2 * Real.pi * (Hf γ w).im * I) * cexp (2 * Real.pi * (Hf γ' w).im * I) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [e]; ring
end ReciprocityTheory.ChartRestriction.G.I2
