-- Prove2me | solution 1 for PI.StabPairsW.col_of_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:27:32.006976+00:00
-- url     : https://prove2.me/submissions/e2e3b9d5-b6d6-4e75-a085-7a7b239e5634

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_ConverseStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_IsUnitDetOfMemGV

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.StabPairsW
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
variable {k r : ℕ}
namespace PI.StabPairsW
theorem _root_.solution (z : Fin (2 * r + k + 1) → ℂ) (s : B.Mat k r) (x : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)
    (h : s * Ff k r z = Ff k r z * x) (b : Fin (r + 1)) : s *ᵥ fvec k r z b = ∑ c, x c b • fvec k r z c := by
  funext i
  have h1 := congrFun (congrFun h i) b
  simp only [Matrix.mul_apply, Ff, Matrix.of_apply] at h1
  simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [h1]
  exact Finset.sum_congr rfl fun c _ => mul_comm _ _
end PI.StabPairsW
