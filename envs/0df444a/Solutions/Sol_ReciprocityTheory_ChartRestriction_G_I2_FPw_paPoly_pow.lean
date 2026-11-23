-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.FPw.paPoly_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:58:38.734129+00:00
-- url     : https://prove2.me/submissions/12099bd2-16f5-4c71-8656-e8a8d056d33b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_PaUContinuous
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_PaPolyTranslate
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_FPw_paPoly_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_FPw_paPoly_const

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
theorem _root_.solution {c : ℕ} {F : EuclideanSpace ℂ ι → ℂ} (hF : F ∈ paPoly c) (n : ℕ) :
    F ^ n ∈ paPoly (n * c) := by
  induction n with
  | zero =>
    rw [pow_zero, zero_mul]
    exact paPoly_const 1
  | succ n ih =>
    rw [pow_succ, add_mul, one_mul]
    exact paPoly_mul ih hF
end ReciprocityTheory.ChartRestriction.G.I2.FPw
