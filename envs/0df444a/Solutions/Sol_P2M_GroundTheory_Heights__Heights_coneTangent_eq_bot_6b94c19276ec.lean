-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_coneTangent_eq_bot_6b94c19276ec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:26:01.888921+00:00
-- url     : https://prove2.me/submissions/d70a7598-3b3f-41ef-8109-4cbd7bdd7b1b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeJacMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsTangentJacCompress
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsKernelProjMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeTangentAverage
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeJacMeasurable
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermNorm_pointOf_eq_zero_1a71672ffe50


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
open MvPolynomial MeasureTheory Module
noncomputable section
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (h : HermNorm n) {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {y : EuclideanSpace ℂ (Fin n)} (hy : y ∉ coneSet h J) : coneTangent h J y = ⊥ := by
  obtain ⟨q, hq, hq0⟩ : ∃ q ∈ J, eval (h.pointOf y) q ≠ 0 := by
    simpa [coneSet] using hy
  rw [eq_bot_iff]
  intro v hv
  rw [Submodule.mem_bot]
  apply h.pointOf_eq_zero
  funext l
  have h1 : ∑ j, eval (h.pointOf y) (pderiv j q) * h.pointOf v j = 0 := hv q hq
  have h2 : ∑ j, eval (h.pointOf y) (pderiv j (X l * q)) * h.pointOf v j = 0 :=
    hv _ (J.mul_mem_left _ hq)
  have h3 : ∀ j, eval (h.pointOf y) (pderiv j (X l * q)) * h.pointOf v j =
      h.pointOf y l * (eval (h.pointOf y) (pderiv j q) * h.pointOf v j) +
        if l = j then eval (h.pointOf y) q * h.pointOf v l else 0 := by
    intro j
    by_cases hj : l = j
    · subst hj
      simp
      ring
    · simp [pderiv_X_of_ne hj, hj]
      ring
  simp only [h3, Finset.sum_add_distrib, ← Finset.mul_sum, h1, mul_zero, zero_add,
    Finset.sum_ite_eq, Finset.mem_univ, if_true] at h2
  exact (mul_eq_zero.1 h2).resolve_left hq0
end GroundTheory.Heights₂.Heights
