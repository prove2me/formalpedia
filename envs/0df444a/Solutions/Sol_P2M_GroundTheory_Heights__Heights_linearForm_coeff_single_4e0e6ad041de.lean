-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_linearForm_coeff_single_4e0e6ad041de
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:34:38.675614+00:00
-- url     : https://prove2.me/submissions/03ceeebc-ce35-4318-be39-82668daca022

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsNormForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PLinearFormPrime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {F : Type} [Field F] {n : ℕ} (a : Fin n → F) (i : Fin n) :
    (∑ m, X m * C (a m) : MvPolynomial (Fin n) F).coeff (Finsupp.single i 1) = a i := by
  classical
  rw [coeff_sum, Finset.sum_eq_single i]
  · rw [mul_comm, coeff_C_mul, coeff_X]
    simp
  · intro j _ hji
    rw [mul_comm, coeff_C_mul, coeff_X, if_neg, mul_zero]
    intro h
    exact hji ((Finsupp.single_left_inj one_ne_zero).mp h)
  · simp
end GroundTheory.Heights₂.Heights
