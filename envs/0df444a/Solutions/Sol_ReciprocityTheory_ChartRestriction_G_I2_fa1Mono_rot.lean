-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.fa1Mono_rot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:16:28.088907+00:00
-- url     : https://prove2.me/submissions/68244e05-2b96-4871-8d9b-78805ae9cf08

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_IntegrableNormPowMulExpNegMulNormSq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_fa1Mono_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_fa1Rot_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution {g : ℕ} (α : Fin g →₀ ℕ) (j : Fin g) (u : Circle)
    (z : EuclideanSpace ℂ (Fin g)) :
    monomialOfMultiindex α (coordinateRotation j u z) = (u : ℂ) ^ (α j) * monomialOfMultiindex α z := by
  rw [fa1Mono_eq, fa1Mono_eq]
  simp only [fa1Rot_apply, mul_pow, Finset.prod_mul_distrib, ite_pow, one_pow,
    Finset.prod_ite_eq', Finset.mem_univ, if_true]
end ReciprocityTheory.ChartRestriction.G.I2
