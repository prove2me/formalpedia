-- Prove2me | solution 1 for PI.KFinSmoothW.qd_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:51:47.99521+00:00
-- url     : https://prove2.me/submissions/fd3c8f24-6922-4c51-9dcc-ea817a229e3d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KFiniteSmoothVectors_UnitaryModelOfMultiplicityGardingDensity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KFiniteSmoothVectors_DenseWeakVectors
import Theorems.Thm_PI_KFinSmoothW_qd_eq_trace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Topology
open scoped InnerProductSpace ContDiff
noncomputable section
open PI PI.KFinSmoothW
open PI.UpqRep
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
namespace PI.KFinSmoothW
theorem _root_.solution (a m : Matrix (Fin n) (Fin n) ℂ) (h1 : a * aᴴ = 1) (h2 : aᴴ * a = 1) :
    qd (a * m * aᴴ) = qd m := by
  rw [qd_eq_trace, qd_eq_trace]
  have e : a * m * aᴴ - 1 = a * (m - 1) * aᴴ := by
    rw [mul_sub, sub_mul, mul_one, h1]
  have e2 : (a * (m - 1) * aᴴ)ᴴ * (a * (m - 1) * aᴴ) = a * ((m - 1)ᴴ * (m - 1)) * aᴴ := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc aᴴ a, h2, Matrix.one_mul]
  rw [e, e2, Matrix.trace_mul_comm, ← Matrix.mul_assoc, h2, Matrix.one_mul]
end PI.KFinSmoothW
