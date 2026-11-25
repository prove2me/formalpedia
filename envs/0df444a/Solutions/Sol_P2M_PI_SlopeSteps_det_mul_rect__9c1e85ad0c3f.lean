-- Prove2me | solution 1 for P2M_PI_SlopeSteps_det_mul_rect__9c1e85ad0c3f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:25:48.382456+00:00
-- url     : https://prove2.me/submissions/7e39d9fc-1712-4eea-b7c9-fc97f24434be

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StandardSlopeBound_MonomialFactorizationLower
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StandardSlopeBound_StdSlopeLowOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StandardSlopeBound_GramMatrixDuality
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StandardSlopeBound_NablaGram
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open PI PI.SlopeSteps
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.L2.DIV Matrix
namespace PI.SlopeSteps
theorem _root_.solution {R : Type*} [CommRing R] {k : ℕ} {n : Type*} [Fintype n]
    (A : Matrix (Fin k) n R) (B : Matrix n (Fin k) R) :
    (A * B).det = ∑ f : Fin k → n, (∏ i, B (f i) i) * (A.submatrix id f).det := by
  simp only [det_apply, mul_apply, Fintype.prod_sum, Finset.smul_sum, submatrix_apply, id]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [Units.smul_def, zsmul_eq_mul, Finset.prod_mul_distrib]
  ring
end PI.SlopeSteps
