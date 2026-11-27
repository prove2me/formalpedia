-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MonomialMapNorm_proof_092e0f3b512a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:02:57.860805+00:00
-- url     : https://prove2.me/submissions/aaa2a8f1-9d2a-4e94-8d3d-70fae62a1ba3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_EvalConeChartMonomialNeZeroBis
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MonomialMapNorm_toFun_pow_be03ad1b6938
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MonomialMapNorm_toFun_mul_60b0240c410a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MonomialMapNorm_isNormalSection_mul_cf8746bbf5eb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MonomialMapNorm_isSmallFor_mul_7d4a8514a9a2

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
namespace GroundTheory.Heights₂.Heights
namespace MonomialMapNorm
theorem _root_.solution : MonomialMapNorm.Statement := by
  intro ι _ _ n P L _ q m r hrq g h hg0 hgs hh0 hhs
  refine ⟨fun s hsN hsS ↦ ⟨?_, MonomialMapNorm.isSmallFor_mul P hrq hgs hhs hsS⟩, fun s₁ s₂ e ↦ ?_⟩
  · have hdeg : (((L.pow q).mul (HermLine.standard n)).pow (m + 1)).deg =
        (L.pow (q * m + r)).deg + ((q - r) • L.deg + (m + 1) • (HermLine.standard n).deg) := by
      funext k
      simp only [HermLine.pow, HermLine.mul, Pi.add_apply, Pi.smul_apply]
      simp only [nsmul_eq_mul]
      push_cast [Nat.cast_sub hrq.le]
      ring
    rw [hdeg]
    simpa only [MonomialMapNorm.toFun_mul, MonomialMapNorm.toFun_pow, mul_assoc] using
      MonomialMapNorm.isNormalSection_mul P hsN ((g.pow (q - r)).mul (h.pow (m + 1)))
  · have hu : g.toFun ^ (q - r) * h.toFun ^ (m + 1) ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ hg0) (pow_ne_zero _ hh0)
    simp only [mul_assoc] at e
    exact mul_right_cancel₀ hu e
end MonomialMapNorm
end GroundTheory.Heights₂.Heights
