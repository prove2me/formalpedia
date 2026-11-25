-- Prove2me | solution 1 for PI.QnRT.mul_exp_dz
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:34:25.266892+00:00
-- url     : https://prove2.me/submissions/01f805b1-d91f-450d-9180-aa3f671b4e71

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusConjugationRule_WColOther
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusConjugationRule_SecondHermitianPartDiagonal
import Theorems.Thm_PI_QnRT_dg_comm
import Theorems.Thm_PI_QnRT_exp_diag2
import Theorems.Thm_PI_QnRT_w_mul_dg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Filter Topology
open scoped ContDiff
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
open PI PI.QnRT
variable {k r : ℕ}
namespace PI.QnRT
theorem _root_.solution (l : Fin r) (a κ : ℂ) (g₁ : Mx k r) (hg₁ : g₁ ∈ Glev k r l.succ) (t : ℝ) :
    w1 k r l a * g₁ * NormedSpace.exp ((t : ℂ) • dz l κ (-star κ)) =
      w1 k r l (a * Complex.exp (t * κ)) * g₁ := by
  have hsm : (t : ℂ) • dz l κ (-star κ) = (diagonal (fun p => if p = eI k r l then (t : ℂ) * κ
      else if p = esI k r l then (t : ℂ) * -star κ else 0) : Mx k r) := by
    unfold dz
    ext p q
    simp only [Matrix.smul_apply, Matrix.diagonal_apply, smul_eq_mul]
    split_ifs <;> simp
  have hconj : Complex.exp ((t : ℂ) * -star κ) = (star (Complex.exp ((t : ℂ) * κ)))⁻¹ := by
    rw [show (t : ℂ) * -star κ = -(star ((t : ℂ) * κ)) by simp, Complex.exp_neg]
    congr 1
    exact Complex.exp_conj _
  rw [hsm, exp_diag2, hconj, Matrix.mul_assoc, ← dg_comm l _ _ g₁ hg₁, ← Matrix.mul_assoc, w_mul_dg]
end PI.QnRT
