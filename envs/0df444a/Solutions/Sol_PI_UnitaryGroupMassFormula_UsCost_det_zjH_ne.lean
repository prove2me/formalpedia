-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCost.det_zjH_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:58:15.748712+00:00
-- url     : https://prove2.me/submissions/1023ad57-8862-4296-adf4-d5151c63fdff

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_LetterSize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_ContinuousBlockMatrixThree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UsCost
namespace PI.UnitaryGroupMassFormula.UsCost
theorem _root_.solution {p s : ℕ} (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (hd : ∀ i, d i ≠ 0) (η : XiH p s σ)
    (Z : G.Mat s) (hZ : G.detM Z ≠ 0) : (ZjH σ d η Z).det ≠ 0 := by
  unfold ZjH Zj headH
  simp only [Matrix.det_mul, blk2, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₁₂,
    Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul, mul_one]
  unfold wP lowW G.upper
  repeat' apply mul_ne_zero
  all_goals first
    | exact hZ
    | (rw [Matrix.det_diagonal]; exact Finset.prod_ne_zero_iff.2 fun i _ => hd i)
    | (have hP : (of fun a b => if σ a = b then (1 : ℂ) else 0) =
          (1 : Matrix (Fin p) (Fin p) ℂ).submatrix σ id := by
         ext a b
         simp [Matrix.one_apply]
       rw [hP, Matrix.det_permute]
       simp)
    | (first | rw [Matrix.det_of_lowerTriangular _ ?_] | rw [Matrix.det_of_lowerTriangular ?_]
       · simp
       · intro i j hij
         have hij' : i < j := hij
         simp [Matrix.one_apply, hij'.ne, not_lt.2 hij'.le])
    | (first | rw [Matrix.det_of_upperTriangular ?_] | rw [Matrix.det_of_upperTriangular _ ?_]
       · simp [G.strictUpper]
       · intro i j hij
         have hij' : j < i := hij
         simp [G.strictUpper, Matrix.one_apply, hij'.ne', not_lt.2 hij'.le])
end PI.UnitaryGroupMassFormula.UsCost
