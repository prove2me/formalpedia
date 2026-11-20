-- Prove2me | solution 1 for QEC.Distillation.BK05T.bk05TRecurrence_fixed_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:24:41.049299+00:00
-- url     : https://prove2.me/submissions/24b25ca7-10b6-4e96-9e0a-faad81a58487

import Theorems.Thm_QEC_Distillation_BK05T_bk05TThreshold_lt_half
import Theorems.Thm_QEC_Distillation_BK05T_bk05TThresholdPolynomial_threshold
import Theorems.Thm_QEC_Distillation_BK05T_bk05TRecurrence_sub_input
import Theorems.Thm_QEC_Distillation_BK05T_bk05TRecurrence_zero
import Theorems.Thm_QEC_Distillation_BK05T_bk05TRecurrence_half
import Theorems.Thm_QEC_Distillation_BK05T_bk05TRecurrence_threshold
section
noncomputable section
namespace QEC
namespace Distillation
namespace BK05T
open Semantics Semantics.Qubit
open OneQubitMagic
private theorem thresholdPolynomial_eq_zero_of_physical
    (epsilon : Real) (hhalf : epsilon <= 1 / 2)
    (hzero : bk05TThresholdPolynomial epsilon = 0) :
    epsilon = bk05TThreshold := by
  have hfactor :
      bk05TThresholdPolynomial epsilon =
        (epsilon - bk05TThreshold) *
          (7 * epsilon + 7 * bk05TThreshold - 7) := by
    calc
      bk05TThresholdPolynomial epsilon =
          bk05TThresholdPolynomial epsilon -
            bk05TThresholdPolynomial bk05TThreshold := by
              have qecertThresholdPolynomialAtThreshold : bk05TThresholdPolynomial bk05TThreshold = 0 :=
                bk05TThresholdPolynomial_threshold
              rw [qecertThresholdPolynomialAtThreshold]
              ring
      _ = (epsilon - bk05TThreshold) *
          (7 * epsilon + 7 * bk05TThreshold - 7) := by
            unfold bk05TThresholdPolynomial
            ring
  rw [hfactor] at hzero
  rcases mul_eq_zero.mp hzero with hroot | hupper
  · exact sub_eq_zero.mp hroot
  · have hthreshold_lt : bk05TThreshold < 1 / 2 := bk05TThreshold_lt_half
    nlinarith
end BK05T
end Distillation
end QEC
end
end

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.BK05T
open Semantics Semantics.Qubit
open OneQubitMagic
namespace QEC.Distillation.BK05T
theorem _root_.solution
    (epsilon : Real) (hzero : 0 <= epsilon) (hhalf : epsilon <= 1 / 2) :
    bk05TRecurrence epsilon = epsilon <->
      epsilon = 0 \/ epsilon = bk05TThreshold \/ epsilon = 1 / 2 := by
  constructor
  · intro hfixed
    have hsub := bk05TRecurrence_sub_input epsilon hzero hhalf
    rw [hfixed] at hsub
    have hproduct :
        epsilon * (1 - epsilon) * (1 - 2 * epsilon) *
            bk05TThresholdPolynomial epsilon = 0 := by
      have hsuccess := bk05T_successProbability_pos epsilon hzero hhalf
      field_simp [hsuccess.ne'] at hsub
      linarith
    rcases mul_eq_zero.mp hproduct with hleft | hpoly
    · rcases mul_eq_zero.mp hleft with hleft | hlinear
      · rcases mul_eq_zero.mp hleft with hepsilon | hcomplement
        · exact Or.inl hepsilon
        · exfalso
          have : epsilon = 1 := by linarith
          linarith
      · exact Or.inr (Or.inr (by linarith))
    · exact Or.inr (Or.inl
        (thresholdPolynomial_eq_zero_of_physical epsilon hhalf hpoly))
  · rintro (rfl | rfl | rfl)
    · exact (show bk05TRecurrence 0 = 0 from bk05TRecurrence_zero)
    · exact bk05TRecurrence_threshold
    · exact bk05TRecurrence_half
end QEC.Distillation.BK05T
