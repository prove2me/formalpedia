-- Prove2me | solution 1 for PI.OddDualWeyl.Jac.block
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:58:58.2348+00:00
-- url     : https://prove2.me/submissions/d9879b3a-8009-40e5-8594-bb38469bd7df

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacobiMinorIdentity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix
noncomputable section
open PI PI.OddDualWeyl PI.OddDualWeyl.Jac
namespace PI.OddDualWeyl.Jac
theorem _root_.solution {R : Type*} [CommRing R] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (A B : Matrix (m ⊕ n) (m ⊕ n) R) (d : R)
    (h : B * A = d • (1 : Matrix (m ⊕ n) (m ⊕ n) R)) :
    B.toBlocks₂₂.det * A.det = d ^ Fintype.card n * A.toBlocks₁₁.det := by
  have hX : (fromBlocks (1 : Matrix m m R) 0 B.toBlocks₂₁ B.toBlocks₂₂) * A =
      fromBlocks A.toBlocks₁₁ A.toBlocks₁₂ 0 (d • (1 : Matrix n n R)) := by
    ext i j
    have hij := congrFun (congrFun h i) j
    rcases i with i | i <;> rcases j with j | j <;>
      first
      | (simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, Matrix.toBlocks₁₁,
          Matrix.toBlocks₁₂, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂]; done)
      | (simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, Matrix.toBlocks₁₁,
          Matrix.toBlocks₁₂, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂] at hij ⊢; exact hij)
  have hdet := congrArg Matrix.det hX
  simp only [det_mul, det_fromBlocks_zero₁₂, det_fromBlocks_zero₂₁, det_one, det_smul, one_mul,
    mul_one] at hdet
  linear_combination hdet
end PI.OddDualWeyl.Jac
