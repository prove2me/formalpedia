-- Prove2me | solution 1 for QEC.Distillation.BK15.Threshold.bk15FixedPolynomial_eq_zero_of_interior_fixed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T04:30:26.335064+00:00
-- url     : https://prove2.me/submissions/f1a73bec-6982-4f5d-a692-a1cf0bbf609c

import Definitions.Def_QEC_Distillation_FifteenQubitH_Recurrence
import Definitions.Def_QEC_Distillation_FifteenQubitH_Threshold
import Theorems.Thm_QEC_Distillation_BK15_Threshold_one_sub_two_mul_bk15Recurrence

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.BK15
open QEC.Distillation.BK15.Threshold
open Semantics Semantics.Qubit
open NoisyInput Protocol Recurrence
open OneQubitMagic
namespace QEC.Distillation.BK15.Threshold
theorem _root_.solution
    {epsilon : Real} (hhalf : epsilon < 1 / 2)
    (hfixed : bk15Recurrence epsilon = epsilon) :
    bk15FixedPolynomial (bk15Bias epsilon) = 0 := by
  have hdenom : 1 + 15 * bk15Bias epsilon ^ 8 ≠ 0 :=
    (bk15Recurrence_denominator_pos epsilon).ne'
  have hbias_ne : bk15Bias epsilon ≠ 0 := by
    unfold bk15Bias
    linarith
  have htransform := one_sub_two_mul_bk15Recurrence epsilon
  rw [hfixed] at htransform
  field_simp [hdenom] at htransform
  have hproduct :
      bk15Bias epsilon * bk15FixedPolynomial (bk15Bias epsilon) = 0 := by
    calc
      bk15Bias epsilon * bk15FixedPolynomial (bk15Bias epsilon) =
          -(bk15Bias epsilon * (1 + 15 * bk15Bias epsilon ^ 8) -
            bk15Bias epsilon ^ 7 * (15 + bk15Bias epsilon ^ 8)) := by
              unfold bk15FixedPolynomial
              ring
      _ = 0 := by
              unfold bk15Bias at htransform ⊢
              ring_nf at htransform ⊢
              linarith
  exact (mul_eq_zero.mp hproduct).resolve_left hbias_ne
end QEC.Distillation.BK15.Threshold
