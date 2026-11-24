-- Prove2me | solution 1 for QnYLeibnizW.hpart2_skew
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:09:45.943399+00:00
-- url     : https://prove2.me/submissions/7ef050a8-e45e-4bee-a6d0-91df1f795243

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
    (hpart2 H Z)ᴴ * H + H * hpart2 H Z = 0 := by
  have hHinv : H⁻¹ = H := Matrix.inv_eq_left_inv hHH
  have hHH' : ∀ X : Matrix (Fin n) (Fin n) ℂ, H * (H * X) = X := fun X => by
    rw [← mul_assoc, hHH, one_mul]
  have hs : star (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I)) := by
    first | (simp; done) | (simp [mul_neg, inv_neg]; done) | (rw [star_div₀, star_one, star_mul', star_ofNat, Complex.star_def, Complex.conj_I, mul_neg, div_neg])
  unfold hpart2
  rw [hHinv, Matrix.conjTranspose_smul, hs, smul_mul_assoc, Matrix.mul_smul, neg_smul, ← smul_neg, ← smul_add]
  have e : -((Z + H * Zᴴ * H)ᴴ * H) + H * (Z + H * Zᴴ * H) = 0 := by
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hHh, add_mul,
      mul_add, mul_assoc, hHH, hHH', mul_one, neg_add]
    abel
  rw [e, smul_zero]
end QnYLeibnizW
