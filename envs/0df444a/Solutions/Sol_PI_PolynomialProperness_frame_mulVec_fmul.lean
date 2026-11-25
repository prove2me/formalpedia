-- Prove2me | solution 1 for PI.PolynomialProperness.frame_mulVec_fmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:07:56.683573+00:00
-- url     : https://prove2.me/submissions/26494601-a7bb-40e3-b23b-ce37e2264a1e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_UnitriangularInversePolynomialBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_AddLeMulPowOfSqLeOfLeMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
open scoped ComplexConjugate
noncomputable section
open PI PI.PolynomialProperness
namespace PI.PolynomialProperness
theorem _root_.solution {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} {σ : B.Mat k r}
    {v : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (h : ∀ b, σ *ᵥ fvec k r z b = fmul k r z v b)
    (c : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (b : Fin (r + 1)) :
    σ *ᵥ fmul k r z c b = fmul k r z (v * c) b := by
  show σ *ᵥ (∑ a, c a b • fvec k r z a) = ∑ a, (v * c) a b • fvec k r z a
  rw [← Matrix.mulVecLin_apply, map_sum]
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec_smul, h, fmul, Finset.smul_sum, smul_smul, Matrix.mul_apply,
    Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun a _ => ?_
  rw [mul_comm (c a b)]
end PI.PolynomialProperness
