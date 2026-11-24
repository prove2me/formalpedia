-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_cb_rho_eq__0ffcd36dceb3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:52:42.814877+00:00
-- url     : https://prove2.me/submissions/0b7958cc-b495-4a40-9cc7-a47acd255738

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_InLieW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_CbStrictMonoOfAnti

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
theorem _root_.solution (Q : M.Par) (π : M.Ty Q) (j : Fin (Q.k - 1)) :
    M.rho Q π (j.1 + 1) = Q.lo (j.1 + 1) + (((π j : Fin _) : ℕ) : ℝ) := by
  unfold M.rho
  rw [dif_pos ⟨by omega, by have := j.isLt; omega⟩]
  first
    | rfl
    | simp
end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
