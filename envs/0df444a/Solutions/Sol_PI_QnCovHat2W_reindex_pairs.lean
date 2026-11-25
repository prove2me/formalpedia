-- Prove2me | solution 1 for PI.QnCovHat2W.reindex_pairs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:25:05.080431+00:00
-- url     : https://prove2.me/submissions/6a790ce1-ea40-4706-9635-de608079e001

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantHatPairReindex_SkipTwoOfGe
import Theorems.Thm_PI_QnCovHat2W_skip_two_of_lt
import Theorems.Thm_PI_QnCovHat2W_skip_two_of_ge

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open PI PI.QnCovHat2W
open Formalism.REAL Formalism.FourierDecayAlt.Q
namespace PI.QnCovHat2W
theorem _root_.solution {m : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]
    (F : (Fin m → Fin (m + 2)) → M) (β β' : Fin (m + 2) → ℂ) :
    ∑ j : Fin (m + 2), ∑ j' : Fin (m + 1),
        ((-1 : ℂ) ^ ((j : ℕ) + (j' : ℕ)) * (β j * β' (j.succAbove j'))) •
          F (fun k => j.succAbove (j'.succAbove k)) =
      ∑ i : Fin (m + 2), ∑ i' : Fin (m + 2),
        if i < i' then ((-1 : ℂ) ^ ((i : ℕ) + (i' : ℕ)) * (β i' * β' i - β i * β' i')) •
          F (skip2 i i') else 0 := by
  have hR : ∀ i : Fin (m + 2), ∑ i' : Fin (m + 2),
      (if i < i' then ((-1 : ℂ) ^ ((i : ℕ) + (i' : ℕ)) * (β i' * β' i - β i * β' i')) •
        F (skip2 i i') else 0) =
      ∑ i' : Fin (m + 2), (if i < i' then ((-1 : ℂ) ^ ((i : ℕ) + (i' : ℕ)) * (β i' * β' i)) •
        F (skip2 i i') else 0) -
      ∑ i' : Fin (m + 2), (if i < i' then ((-1 : ℂ) ^ ((i : ℕ) + (i' : ℕ)) * (β i * β' i')) •
        F (skip2 i i') else 0) := by
    intro i
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i' _ => ?_
    split_ifs
    · rw [mul_sub, sub_smul]
    · rw [sub_zero]
  have hL : ∀ j : Fin (m + 2), ∑ j' : Fin (m + 1),
      ((-1 : ℂ) ^ ((j : ℕ) + (j' : ℕ)) * (β j * β' (j.succAbove j'))) •
        F (fun k => j.succAbove (j'.succAbove k)) =
      ∑ i : Fin (m + 2), (if i < j then ((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ)) * (β j * β' i)) •
        F (skip2 i j) else 0) -
      ∑ i' : Fin (m + 2), (if j < i' then ((-1 : ℂ) ^ ((j : ℕ) + (i' : ℕ)) * (β j * β' i')) •
        F (skip2 j i') else 0) := by
    intro j
    rw [Fin.sum_univ_castSucc (f := fun i => if i < j then ((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ)) *
        (β j * β' i)) • F (skip2 i j) else 0),
      Fin.sum_univ_succ (f := fun i' => if j < i' then ((-1 : ℂ) ^ ((j : ℕ) + (i' : ℕ)) *
        (β j * β' i')) • F (skip2 j i') else 0)]
    simp only [not_lt.mpr (Fin.le_last j), Fin.not_lt_zero, if_false, add_zero, zero_add]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j' _ => ?_
    by_cases h : Fin.castSucc j' < j
    · have h' : ¬ j < j'.succ := by
        rw [← Fin.le_castSucc_iff]
        exact not_le.mpr h
      rw [if_pos h, if_neg h', sub_zero, Fin.succAbove_of_castSucc_lt _ _ h, skip_two_of_lt j j' h,
        Fin.val_castSucc]
      congr 1
      ring
    · have hle : j ≤ Fin.castSucc j' := not_lt.mp h
      have h' : j < j'.succ := Fin.le_castSucc_iff.mp hle
      rw [if_neg h, if_pos h', zero_sub, Fin.succAbove_of_le_castSucc _ _ hle, skip_two_of_ge j j' hle,
        Fin.val_succ, ← neg_smul]
      congr 1
      ring
  rw [Finset.sum_congr rfl fun j _ => hL j, Finset.sum_sub_distrib,
    Finset.sum_congr rfl fun i _ => hR i, Finset.sum_sub_distrib]
  congr 1
  rw [Finset.sum_comm]
end PI.QnCovHat2W
