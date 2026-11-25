-- Prove2me | solution 1 for QnYLeibnizW.hasDerivAt_ybv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:04:18.428636+00:00
-- url     : https://prove2.me/submissions/8117a29b-8229-4e5e-9237-3053f33efd9a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ConjugateTransposeLeibniz_ExpMulVecFix
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ConjugateTransposeLeibniz_YOperatorLeibnizRule
import Theorems.Thm_Formalism_REAL_hasDerivAt_matrix_exp_smul_at_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
namespace QnYLeibnizW
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
section Gen
variable {n : ℕ}
end Gen
section Pos
variable {k r : ℕ} {i : Fin (r + 1)}
end Pos
section Deriv
variable {k r : ℕ} {i : Fin (r + 1)}
private theorem hasDerivAt_mul_exp_smul_zero' {n : ℕ} (g X : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) (g * X) 0 := by
  let large₂ : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ := LinearMap.toContinuousLinearMap
    { toFun := fun M => g * M
      map_add' := fun M N => Matrix.mul_add g M N
      map_smul' := fun c M => by simp [Matrix.mul_smul] }
  have h := large₂.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_matrix_exp_smul_at_zero X)
  exact h
end Deriv
end QnYLeibnizW
end
end

set_option autoImplicit false
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
open QnYLeibnizW
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {i : Fin (r + 1)}
namespace QnYLeibnizW
theorem _root_.solution (z : Fin (2 * r + k + 1) → ℂ) (c : Fin (mdim k r i)) (g X : Mx k r) :
    HasDerivAt (fun t : ℝ => ybv k r z i (g * NormedSpace.exp ((t : ℂ) • X)) c)
      (herm (Hpk k r) ((g * X) *ᵥ bvec (posL k r i c)) (fvec k r z i)) 0 := by
  have h := (hermL (Hpk k r) (bvec (posL k r i c)) (fvec k r z i)).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
    (hasDerivAt_mul_exp_smul_zero' g X)
  exact h
end QnYLeibnizW
