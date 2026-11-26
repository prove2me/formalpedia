-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.pa_one_add_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T03:37:12.761531+00:00
-- url     : https://prove2.me/submissions/425b68be-7b97-4411-b4a7-4a76ba676879

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_CardSupportLeAndSumTwoPowLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_IntegrableNormPowMulExpNegMulNormSq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropAA
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
open Classical
theorem _root_.solution (n : ℕ) {t : ℝ} (ht : 0 ≤ t) : (1 + t) ^ n ≤ 2 ^ n * (1 + t ^ n) := by
  first
    | (have h1 : (1 + t) ≤ 2 * max 1 t := by
         have a := le_max_left (1:ℝ) t
         have b := le_max_right (1:ℝ) t
         linarith
       have h2 : (max 1 t) ^ n ≤ 1 + t ^ n := by
         rcases le_total t 1 with h | h
         · rw [max_eq_left h, one_pow]
           have := pow_nonneg ht n
           linarith
         · rw [max_eq_right h]; linarith
       calc (1 + t) ^ n ≤ (2 * max 1 t) ^ n := pow_le_pow_left₀ (by linarith) h1 n
         _ = 2 ^ n * (max 1 t) ^ n := mul_pow _ _ _
         _ ≤ 2 ^ n * (1 + t ^ n) := mul_le_mul_of_nonneg_left h2 (by positivity))

