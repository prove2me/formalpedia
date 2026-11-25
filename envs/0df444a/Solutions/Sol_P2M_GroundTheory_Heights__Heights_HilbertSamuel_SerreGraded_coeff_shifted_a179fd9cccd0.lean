-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_SerreGraded_coeff_shifted_a179fd9cccd0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:40:51.746183+00:00
-- url     : https://prove2.me/submissions/d5f94109-337e-4583-8590-1a9862d6aa3b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsSerreGraded
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PSerreGraded
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_SerreGraded_coeff_mem_afe1aca3377d

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
noncomputable section
open GroundTheory.Heights₂.Heights.HilbertSamuel.SerreGraded
open Polynomial
variable {Ω : Type} [Field Ω] {q r : ℕ} (w : Fin q → Ω) (d : Fin r → ℕ) (t : Fin r → Ω)
variable [Algebra (MvPolynomial (Fin q) ℤ) (Polynomial Ω)]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.SerreGraded
theorem _root_.solution (hA : algebraMap (MvPolynomial (Fin q) ℤ) (Polynomial Ω) = act w) (u : Fin q) {y : (Polynomial Ω)}
    (hy : y ∈ shifted w d t u) (k : ℕ) : ∃ z ∈ gradedSpan w d t k, y.coeff (k + 1) = w u * z := by
  obtain ⟨m, hm, rfl⟩ := Submodule.mem_map.mp hy
  refine ⟨m.coeff k, coeff_mem w d t hA hm k, ?_⟩
  rw [LinearMap.mulLeft_apply, mul_assoc, coeff_C_mul, coeff_X_mul]
end GroundTheory.Heights₂.Heights.HilbertSamuel.SerreGraded
