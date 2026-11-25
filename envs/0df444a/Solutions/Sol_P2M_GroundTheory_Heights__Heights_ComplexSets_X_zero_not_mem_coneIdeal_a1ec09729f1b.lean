-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ComplexSets_X_zero_not_mem_coneIdeal_a1ec09729f1b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:29:11.095727+00:00
-- url     : https://prove2.me/submissions/f5c0421d-8e94-4ebb-b98a-df48257eba1f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_coneEq_ne_zero_df5d0619dfe6

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
open MvPolynomial Pointwise
noncomputable section
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.ComplexSets
theorem _root_.solution : (X 0 : MvPolynomial (Fin 3) ℂ) ∉ coneIdeal := by
  intro h
  obtain ⟨q, hq⟩ := Ideal.mem_span_singleton'.mp h
  have hq0 : q ≠ 0 := by
    rintro rfl
    exact X_ne_zero (0 : Fin 3) (by rw [← hq, zero_mul])
  have hhom : coneEq.IsHomogeneous 2 :=
    (isHomogeneous_X_pow (0 : Fin 3) 2).sub ((isHomogeneous_X ℂ (1 : Fin 3)).mul
      (isHomogeneous_X ℂ (2 : Fin 3)))
  have h := congrArg totalDegree hq
  rw [totalDegree_mul_of_isDomain hq0 coneEq_ne_zero, hhom.totalDegree coneEq_ne_zero,
    totalDegree_X] at h
  omega
end GroundTheory.Heights₂.Heights.ComplexSets
