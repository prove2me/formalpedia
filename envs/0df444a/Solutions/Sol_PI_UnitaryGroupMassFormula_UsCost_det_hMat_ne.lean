-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCost.det_hMat_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:18:06.671154+00:00
-- url     : https://prove2.me/submissions/211457d8-bf90-4d36-8d4e-6574dd7bee05

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_LetterSize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_Smooth
import Theorems.Thm_P2M_PI_UnitaryGroupMassFormula_UsCost_permutationMatrix_eq_permMatrix__665b2f5dbc76

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UsCost
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : WithTop ℕ∞} {x₀ : X}
variable {k p s ρ : ℕ} {σ : Equiv.Perm (Fin p)} {d : Fin p → ℂ}
namespace PI.UnitaryGroupMassFormula.UsCost
theorem _root_.solution (hd : ∀ i, d i ≠ 0) : (hMat σ d).det ≠ 0 := by
  rw [hMat, Matrix.det_mul, permutationMatrix_eq_permMatrix', Matrix.det_permutation, Matrix.det_diagonal]
  refine mul_ne_zero ?_ (Finset.prod_ne_zero_iff.2 fun i _ => hd i)
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
end PI.UnitaryGroupMassFormula.UsCost
