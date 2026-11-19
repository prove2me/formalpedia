-- Prove2me | solution 1 for QEC.Distillation.BK15.Threshold.bk15Recurrence_fixed_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T04:34:07.542601+00:00
-- url     : https://prove2.me/submissions/5642d0f8-6d22-425c-ba40-d66642b146b3

import Definitions.Def_QEC_Distillation_FifteenQubitH_Recurrence
import Definitions.Def_QEC_Distillation_FifteenQubitH_Threshold
import Theorems.Thm_QEC_Distillation_BK15_Threshold_bk15Recurrence_zero
import Theorems.Thm_QEC_Distillation_BK15_Threshold_bk15Recurrence_half
import Theorems.Thm_QEC_Distillation_BK15_Threshold_bk15FixedPolynomial_eq_zero_of_interior_fixed
import Theorems.Thm_QEC_Distillation_BK15_Threshold_bk15Recurrence_epsilonStar
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm


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
    (epsilon : Real) (hzero : 0 <= epsilon) (hhalf : epsilon <= 1 / 2) :
    bk15Recurrence epsilon = epsilon ↔
      epsilon = 0 ∨ epsilon = epsilonStar ∨ epsilon = 1 / 2 := by
  constructor
  · intro hfixed
    rcases eq_or_lt_of_le hzero with hepsilon | hpositive
    · exact Or.inl hepsilon.symm
    rcases eq_or_lt_of_le hhalf with hhalf_eq | hlt_half
    · exact Or.inr (Or.inr hhalf_eq)
    have hroot := bk15FixedPolynomial_eq_zero_of_interior_fixed
      hlt_half hfixed
    have hbias_pos : 0 < bk15Bias epsilon := by
      unfold bk15Bias
      linarith
    have hbias_one : bk15Bias epsilon < 1 := by
      unfold bk15Bias
      linarith
    have heq_bias : bk15Bias epsilon = bk15BiasStar :=
      fixedPolynomial_root_unique_in_unitInterval
        hbias_pos hbias_one bk15BiasStar_pos bk15BiasStar_lt_one
        hroot bk15FixedPolynomial_biasStar
    right; left
    rw [← bk15Bias_epsilonStar] at heq_bias
    unfold bk15Bias at heq_bias
    linarith
  · rintro (rfl | rfl | rfl)
    · exact bk15Recurrence_zero
    · exact bk15Recurrence_epsilonStar
    · exact bk15Recurrence_half
end QEC.Distillation.BK15.Threshold
