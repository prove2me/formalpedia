-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.FPw.paU_continuous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:35:38.580273+00:00
-- url     : https://prove2.me/submissions/de373915-4bf7-4425-bd94-79cf1da4fd92

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_HfEqInner
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_PaUContinuous
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_FPw_Hf_continuous
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_paPoly_continuous


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
theorem _root_.solution {q c : ℕ} (a : EuclideanSpace ℂ ι) {F : EuclideanSpace ℂ ι → ℂ}
    (hF : F ∈ paPoly c) : Continuous (paU q a F) := by
  unfold paU
  exact (Complex.continuous_exp.comp ((continuous_const.mul (Hf_continuous a)).sub continuous_const)).mul
    ((paPoly_continuous hF).comp (continuous_id.sub continuous_const))
end ReciprocityTheory.ChartRestriction.G.I2.FPw
