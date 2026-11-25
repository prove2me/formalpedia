-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_ChartNormPts_aeval_homogenise_div_0794543b621c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:13:34.411835+00:00
-- url     : https://prove2.me/submissions/555f3372-399f-4562-b5ec-ab807e9bb2fc

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsIntersectionFamily
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PChartNormPtsA
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ChartNormPts_aeval_homogenise_dacb91173eef

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open GroundTheory.Heights₂.Heights.Inter.ChartNormPts
variable {P : Type*} {Q : Type*} [Fintype Q] {V : Type*}
namespace GroundTheory.Heights₂.Heights.Inter.ChartNormPts
theorem _root_.solution {L : Type*} [Field L] (v : P → V) (f g : Q → V)
    (F : MvPolynomial Q (MvPolynomial P ℤ)) (x : V → L) (hx : ∀ q, x (g q) ≠ 0) :
    aeval x (homogenise v f g F) =
      (∏ q, x (g q) ^ degreeOf q F) *
        eval₂ (aeval (x ∘ v) : MvPolynomial P ℤ →ₐ[ℤ] L).toRingHom (fun q => x (f q) / x (g q)) F := by
  rw [aeval_homogenise, eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  rw [mul_left_comm, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun q _ => ?_
  rw [div_pow, ← pow_mul_pow_sub (x (g q)) (monomial_le_degreeOf q hμ)]
  field_simp [pow_ne_zero _ (hx q)]
end GroundTheory.Heights₂.Heights.Inter.ChartNormPts
