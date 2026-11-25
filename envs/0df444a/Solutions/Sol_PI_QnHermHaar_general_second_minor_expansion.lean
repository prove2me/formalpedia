-- Prove2me | solution 1 for PI.QnHermHaar.general_second_minor_expansion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:22:44.825693+00:00
-- url     : https://prove2.me/submissions/056e162b-2830-4321-8b3b-dd2ff0d308ac

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_SumFourCommVersion
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_GeneralSecondMinorExpansion
import Theorems.Thm_PI_QnHermHaar_pull6
import Theorems.Thm_PI_QnHermHaar_sumSingle
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Finset
noncomputable section
namespace PI.QnHermHaar
open Formalism.REAL Formalism.FourierDecayAlt.Q
private theorem sum_mul_sum_mul_eq_sum_sum {A : Type*} [Ring A] {m : ℕ} (f g : Fin m → A) (q : A) :
    (∑ l, f l) * (∑ p, g p) * q = ∑ l, ∑ p, f l * g p * q := by
  simp only [Finset.mul_sum, Finset.sum_mul]
  try (first | rfl | exact Finset.sum_comm)
end PI.QnHermHaar
end
end

set_option autoImplicit false
open Matrix Finset
noncomputable section
open PI PI.QnHermHaar
open Formalism.REAL Formalism.FourierDecayAlt.Q
namespace PI.QnHermHaar
theorem _root_.solution {A : Type*} [Ring A] [Algebra ℂ A] {m : ℕ} (E : Fin m → Fin m → A) (W V : Fin m → A) (w : ℂ)
    (a' β' : Fin m → ℂ) :
    ∑ l, ∑ p, W l * V p * chat2A E w (Pi.single p 1) a' (Pi.single l 1) β' =
      ∑ i : Fin m, ∑ i' : Fin m, ∑ j : Fin m, ∑ j' : Fin m,
        if i < i' ∧ j < j' then
          ((-1 : ℂ) ^ ((i : ℕ) + (i' : ℕ) + (j : ℕ) + (j' : ℕ))) •
            ((W i * algebraMap ℂ A (β' i') - W i' * algebraMap ℂ A (β' i)) *
              (V j * algebraMap ℂ A (a' j') - V j' * algebraMap ℂ A (a' j)) *
              qminor E (skip2 i i') (skip2 j j') w)
        else 0 := by
  simp only [chat2A, Finset.mul_sum, mul_ite, mul_zero]
  refine (pull6 _).trans ?_
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ =>
    Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
  by_cases h : i < i' ∧ j < j'
  · simp only [if_pos h]
    rw [sumSingle W β' i i', sumSingle V a' j j', sum_mul_sum_mul_eq_sum_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
    congr 1
    ring
  · simp only [if_neg h, Finset.sum_const_zero]
end PI.QnHermHaar
