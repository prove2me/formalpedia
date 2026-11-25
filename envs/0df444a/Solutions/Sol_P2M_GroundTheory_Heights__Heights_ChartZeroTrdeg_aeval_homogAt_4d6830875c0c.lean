-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartZeroTrdeg_aeval_homogAt_4d6830875c0c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:32:06.515406+00:00
-- url     : https://prove2.me/submissions/a298f766-bd3d-4945-96ea-62604c01f2b7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsChartZeroTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_ImportsAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PChartZeroTrdeg
import Theorems.Thm_GroundTheory_Arith_Toric_LowerBound_sum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.ChartZeroTrdeg
variable {F : Type} [Field F] {n : ℕ}
namespace GroundTheory.Heights₂.Heights.ChartZeroTrdeg
theorem _root_.solution {L : Type} [Field L] [Algebra F L] (p : MvPolynomial (Fin n) F) (j : Fin n)
    (N : ℕ) (hN : p.totalDegree ≤ N) (z : Fin n → L) (hz : z j ≠ 0) :
    aeval z (homogAt p j N) = z j ^ N * aeval (fun m => z m * (z j)⁻¹) p := by
  conv_rhs => rw [p.as_sum]
  rw [homogAt, map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α hα => ?_
  have hk := (le_totalDegree hα).trans hN
  simp only [map_mul, aeval_monomial, map_pow, aeval_X, mul_pow, Finsupp.prod_mul]
  have hc : (α.prod fun a => HPow.hPow (z j)⁻¹) = (z j)⁻¹ ^ (α.sum fun _ e => e) := by
    simp only [Finsupp.prod, Finsupp.sum]
    exact Finset.prod_pow_eq_pow_sum _ _ _
  rw [hc]
  have : z j ^ N = z j ^ (N - α.sum fun _ e => e) * z j ^ (α.sum fun _ e => e) := by
    rw [← pow_add, Nat.sub_add_cancel hk]
  rw [this, inv_pow]
  field_simp
end GroundTheory.Heights₂.Heights.ChartZeroTrdeg
