-- Prove2me | solution 1 for PI.SlopeSteps.factorial_mul_det_gram_cauchy_binet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:33:16.473074+00:00
-- url     : https://prove2.me/submissions/7fd6548f-9d10-4a2a-a69a-ce36a7d1687d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StandardSlopeBound_MonomialFactorizationLower
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StandardSlopeBound_StdSlopeLowOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StandardSlopeBound_GramMatrixDuality
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StandardSlopeBound_NablaGram
import Theorems.Thm_P2M_PI_SlopeSteps_det_mul_rect__9c1e85ad0c3f
import Theorems.Thm_P2M_PI_SlopeSteps_sum_comp_perm__6a20aaa6ea80
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
theorem _root_.solution {R : Type*} [CommRing R] (k : ℕ) {n : Type*} [Fintype n] [DecidableEq n]
    (q : n → R) (V : Matrix n (Fin k) R) :
    (k.factorial : R) * (Vᵀ * diagonal q * V).det =
      ∑ f : Fin k → n, (∏ i, q (f i)) * ((V.submatrix f id).det * (Vᵀ.submatrix id f).det) := by
  have hexp : (Vᵀ * diagonal q * V).det = ∑ f : Fin k → n, (∏ i, q (f i)) *
      ((∏ i, V (f i) i) * (Vᵀ.submatrix id f).det) := by
    rw [Matrix.mul_assoc, det_mul_rect']
    refine Finset.sum_congr rfl fun f _ => ?_
    simp only [diagonal_mul, Finset.prod_mul_distrib, mul_assoc]
  have hk : (k.factorial : R) = ∑ _τ : Equiv.Perm (Fin k), (1 : R) := by
    simp [Fintype.card_perm]
  have step : ∀ τ : Equiv.Perm (Fin k),
      (1 : R) * ∑ f : Fin k → n, (∏ i, q (f i)) * ((∏ i, V (f i) i) * (Vᵀ.submatrix id f).det)
        = ∑ f : Fin k → n, (∏ i, q (f i)) *
            ((∏ i, V (f (τ i)) i) * ((Vᵀ.submatrix id f).submatrix id τ).det) := by
    intro τ
    rw [one_mul, ← sum_comp_perm' _ τ]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [Equiv.prod_comp τ (fun i => q (f i))]
    rfl
  rw [hexp, hk, Finset.sum_mul, Finset.sum_congr rfl fun τ _ => step τ, Finset.sum_comm]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [← Finset.mul_sum]
  congr 1
  rw [det_apply (V.submatrix f id), Finset.sum_mul]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [det_permute']
  simp only [submatrix_apply, id, Units.smul_def, zsmul_eq_mul]
  ring
end PI.SlopeSteps
