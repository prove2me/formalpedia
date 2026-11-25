-- Prove2me | solution 1 for QnYLeibnizW.hasDerivAt_yv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:04:19.561807+00:00
-- url     : https://prove2.me/submissions/a395486b-a1a6-4a40-8c32-2de000d783c7

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
    HasDerivAt (fun t : ℝ => yv k r z i (g * NormedSpace.exp ((t : ℂ) • X)) c)
      (-((X *ᵥ (g⁻¹ *ᵥ fvec k r z i)) (posL k r i c))) 0 := by
  have hfun : (fun t : ℝ => yv k r z i (g * NormedSpace.exp ((t : ℂ) • X)) c) =
      fun t : ℝ => evL (g⁻¹ *ᵥ fvec k r z i) (posL k r i c) (NormedSpace.exp ((t : ℂ) • (-X))) := by
    funext t
    show ((g * NormedSpace.exp ((t : ℂ) • X))⁻¹ *ᵥ fvec k r z i) (posL k r i c) =
      (NormedSpace.exp ((t : ℂ) • (-X)) *ᵥ (g⁻¹ *ᵥ fvec k r z i)) (posL k r i c)
    rw [Matrix.mulVec_mulVec, smul_neg, Matrix.exp_neg, ← Matrix.mul_inv_rev]
  rw [hfun]
  have h := (evL (g⁻¹ *ᵥ fvec k r z i) (posL k r i c)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_matrix_exp_smul_at_zero (-X))
  refine h.congr_deriv ?_
  show ((-X) *ᵥ (g⁻¹ *ᵥ fvec k r z i)) (posL k r i c) = -((X *ᵥ (g⁻¹ *ᵥ fvec k r z i)) (posL k r i c))
  rw [Matrix.neg_mulVec]
  rfl
end QnYLeibnizW
