-- Prove2me | solution 1 for PI.StabPairsW.mul_of_col
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:58:08.064575+00:00
-- url     : https://prove2.me/submissions/a80d59be-dc77-4efe-b25f-cf3d606c13c4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_IsUnitDetOfMemGV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_Forward

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
    (h : ∀ b, s *ᵥ fvec k r z b = ∑ c, x c b • fvec k r z c) : s * Ff k r z = Ff k r z * x := by
  ext i b
  have hb := congrFun (h b) i
  simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hb
  simp only [Matrix.mul_apply, Ff, Matrix.of_apply, hb]
  exact Finset.sum_congr rfl fun c _ => mul_comm _ _
end PI.StabPairsW
