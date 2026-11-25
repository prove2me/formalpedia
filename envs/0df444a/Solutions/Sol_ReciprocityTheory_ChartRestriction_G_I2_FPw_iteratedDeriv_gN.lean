-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.FPw.iteratedDeriv_gN
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:41:42.127726+00:00
-- url     : https://prove2.me/submissions/6ce416a5-83eb-4741-81a6-78947f34a67f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_PaPolyTranslate
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_IteratedFDerivTailZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_FPw_deriv_gN
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_FPw_gN_zero

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
theorem _root_.solution : ∀ i N : ℕ, i ≤ N → iteratedDeriv i (gN N) 0 = 0 := by
  intro i
  induction i with
  | zero => intro N _; rw [iteratedDeriv_zero]; exact gN_zero N
  | succ i ih =>
    intro N hN
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    rw [iteratedDeriv_succ', deriv_gN]
    exact ih M (by omega)
end ReciprocityTheory.ChartRestriction.G.I2.FPw
