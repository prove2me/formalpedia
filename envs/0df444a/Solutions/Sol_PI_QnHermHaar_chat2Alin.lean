-- Prove2me | solution 1 for PI.QnHermHaar.chat2Alin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:08:20.351705+00:00
-- url     : https://prove2.me/submissions/ba8cd064-347b-4a8d-b4e9-f7d49691bb3c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_SumFourCommVersion
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_GeneralSecondMinorExpansion
import Theorems.Thm_PI_QnHermHaar_pull6
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
private theorem mul_sum_mul_sum_eq_sum_sum {m : ℕ} (a : ℂ) (f g : Fin m → ℂ) :
    a * (∑ l, f l) * (∑ p, g p) = ∑ l, ∑ p, a * f l * g p := by
  simp only [Finset.mul_sum, Finset.sum_mul]
  try (first | rfl | exact Finset.sum_comm)
private theorem sub_mul_eq_sum_single_sub_mul {m : ℕ} (β c : Fin m → ℂ) (i i' : Fin m) :
    β i * c i' - β i' * c i =
      ∑ l, β l * ((Pi.single l (1 : ℂ) : Fin m → ℂ) i * c i' - (Pi.single l (1 : ℂ) : Fin m → ℂ) i' * c i) := by
  simp [Pi.single_apply, mul_sub, Finset.sum_sub_distrib, ite_mul, mul_ite]
end PI.QnHermHaar
end
end

set_option autoImplicit false
open Matrix Finset
noncomputable section
open PI PI.QnHermHaar
open Formalism.REAL Formalism.FourierDecayAlt.Q
namespace PI.QnHermHaar
theorem _root_.solution {A : Type*} [Ring A] [Algebra ℂ A] {m : ℕ} (E : Fin m → Fin m → A) (w : ℂ)
    (a a' β β' : Fin m → ℂ) :
    chat2A E w a a' β β' = ∑ l, ∑ p, (β l * a p) • chat2A E w (Pi.single p 1) a' (Pi.single l 1) β' := by
  simp only [chat2A, Finset.smul_sum, smul_ite, smul_zero, smul_smul]
  refine Eq.trans ?_ (pull6 _).symm
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ =>
    Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
  by_cases h : i < i' ∧ j < j'
  · simp only [if_pos h]
    simp only [← Finset.sum_smul]
    congr 1
    rw [sub_mul_eq_sum_single_sub_mul β β' i i', sub_mul_eq_sum_single_sub_mul a a' j j', mul_sum_mul_sum_eq_sum_sum]
    exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun p _ => by ring
  · simp only [if_neg h, Finset.sum_const_zero]
end PI.QnHermHaar
