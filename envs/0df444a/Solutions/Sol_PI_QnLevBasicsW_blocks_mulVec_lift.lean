-- Prove2me | solution 1 for PI.QnLevBasicsW.blocks_mulVec_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:57:28.297562+00:00
-- url     : https://prove2.me/submissions/dab6d918-6db0-4de4-9afa-cd8f1e172fff

import Definitions.Def_Formalism_FormalDegreeBessel_StatementRP
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelLiftBasics_SplitInvInjective
import Theorems.Thm_PI_QnLevBasicsW_liftVec_eq

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
open PI PI.QnLevBasicsW
open Formalism.QuantumDeterminants
variable {k i r' : ℕ}
namespace PI.QnLevBasicsW
theorem _root_.solution (A : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ)
    (J : Matrix (Fin (2 * i)) (Fin (2 * i)) ℂ) (v : Fin (2 * r' + k + 1) → ℂ) :
    (fromBlocks A 0 0 J).submatrix (split k i r') (split k i r') *ᵥ liftVec k i r' v =
      liftVec k i r' (A *ᵥ v) := by
  rw [liftVec_eq, liftVec_eq, Matrix.submatrix_mulVec_equiv]
  simp only [Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id]
  rw [Matrix.fromBlocks_mulVec]
  congr 1
  funext x
  rcases x with x | x <;> simp
end PI.QnLevBasicsW
