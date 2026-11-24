-- Prove2me | solution 1 for QnYLeibnizW.hpart1_skew
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:09:44.728344+00:00
-- url     : https://prove2.me/submissions/867d9653-c1e8-4e1b-9aff-f89363b0847d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ConjugateTransposeLeibniz_ExpMulVecFix
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ConjugateTransposeLeibniz_YOperatorLeibnizRule

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
variable {n : ℕ}
namespace QnYLeibnizW
theorem _root_.solution (H Z : Matrix (Fin n) (Fin n) ℂ) (hHh : Hᴴ = H) (hHH : H * H = 1) :
    (hpart1 H Z)ᴴ * H + H * hpart1 H Z = 0 := by
  have hHinv : H⁻¹ = H := Matrix.inv_eq_left_inv hHH
  have hHH' : ∀ X : Matrix (Fin n) (Fin n) ℂ, H * (H * X) = X := fun X => by
    rw [← mul_assoc, hHH, one_mul]
  have hs : star (1 / 2 : ℂ) = 1 / 2 := by simp
  unfold hpart1
  rw [hHinv, Matrix.conjTranspose_smul, hs, smul_mul_assoc, Matrix.mul_smul, ← smul_add]
  have e : (Z - H * Zᴴ * H)ᴴ * H + H * (Z - H * Zᴴ * H) = 0 := by
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hHh, sub_mul,
      mul_sub, mul_assoc, hHH, hHH', mul_one]
    abel
  rw [e, smul_zero]
end QnYLeibnizW
