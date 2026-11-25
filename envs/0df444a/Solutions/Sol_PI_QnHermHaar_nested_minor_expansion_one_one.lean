-- Prove2me | solution 1 for PI.QnHermHaar.nested_minor_expansion_one_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:41:50.706872+00:00
-- url     : https://prove2.me/submissions/5c26a011-1260-423b-99d8-ccc1cb42b38e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_NestedMinorExpansionOneZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_LowerRightNeZeroOfUpperRightZero
import Theorems.Thm_PI_QnHermHaar_mulAM
import Theorems.Thm_PI_QnHermHaar_pairSum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open PI PI.QnHermHaar
open Formalism.REAL Formalism.FourierDecayAlt.Q
namespace PI.QnHermHaar
theorem _root_.solution {A : Type*} [Ring A] [Algebra ℂ A] {t : ℕ} (E : Fin (t + 2) → Fin (t + 2) → A)
    (Y Yb : Fin (t + 2) → A) (x xb : Fin (t + 2) → ℂ) (u : ℂ) :
    tA E Y Yb x xb u 1 1 = -∑ i : Fin (t + 2), ∑ k : Fin (t + 1), ∑ j : Fin (t + 2), ∑ l : Fin (t + 1),
      ((-1 : ℂ) ^ ((i : ℕ) + (k : ℕ)) * (-1 : ℂ) ^ ((j : ℕ) + (l : ℕ)) * xb i * x j) •
        (Yb (i.succAbove k) * Y (j.succAbove l) *
          qminor E (i.succAbove ∘ k.succAbove) (j.succAbove ∘ l.succAbove) (u - 1)) := by
  simp only [tA]
  congr 1

  set G : (Fin t → Fin (t + 2)) → A := fun s => ∑ j : Fin (t + 2), ∑ j' : Fin (t + 2),
    (if j < j' then ((-1 : ℂ) ^ ((j : ℕ) + (j' : ℕ))) •
      ((Y j * algebraMap ℂ A (x j') - Y j' * algebraMap ℂ A (x j)) * qminor E s (skip2 j j') (u - 1)) else 0)
    with hG
  have h1 : ∀ i i' : Fin (t + 2), (∑ j : Fin (t + 2), ∑ j' : Fin (t + 2),
      if i < i' ∧ j < j' then
        ((-1 : ℂ) ^ ((i : ℕ) + (i' : ℕ) + (j : ℕ) + (j' : ℕ))) •
          ((Yb i * algebraMap ℂ A (xb i') - Yb i' * algebraMap ℂ A (xb i)) *
            (Y j * algebraMap ℂ A (x j') - Y j' * algebraMap ℂ A (x j)) *
            qminor E (skip2 i i') (skip2 j j') (u - 1))
      else 0) =
      if i < i' then ((-1 : ℂ) ^ ((i : ℕ) + (i' : ℕ))) •
        ((Yb i * algebraMap ℂ A (xb i') - Yb i' * algebraMap ℂ A (xb i)) * G (skip2 i i')) else 0 := by
    intro i i'
    by_cases hi : i < i'
    · simp only [hi, true_and, if_true, hG, Finset.mul_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun j' _ => ?_))
      split_ifs
      · rw [mul_smul_comm, smul_smul, ← pow_add, mul_assoc]
        congr 2
        ring
      · simp
    · simp [hi]
  simp only [h1]
  have hp := pairSum Yb (fun i => algebraMap ℂ A (xb i)) G
  try simp only at hp
  rw [hp]
  have hq : ∀ s : Fin t → Fin (t + 2), G s = ∑ j : Fin (t + 2), ∑ l : Fin (t + 1),
      ((-1 : ℂ) ^ ((j : ℕ) + (l : ℕ))) • (Y (j.succAbove l) * algebraMap ℂ A (x j) *
        qminor E s (j.succAbove ∘ l.succAbove) (u - 1)) := by
    intro s
    have h := pairSum Y (fun j => algebraMap ℂ A (x j)) (fun s' => qminor E s s' (u - 1))
    rw [hG]
    exact h
  simp only [hq, Finset.mul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ =>
    Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun l _ => ?_))))
  simp only [mulAM, smul_mul_assoc, mul_smul_comm, smul_smul, mul_assoc]
  congr 1
  ring
end PI.QnHermHaar
