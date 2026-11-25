-- Prove2me | solution 1 for P2M_ReciprocityTheory_AnForm_A_mixedCof_diag__b2efbf315574
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:14:37.011375+00:00
-- url     : https://prove2.me/submissions/66c5f519-0bab-493a-af6e-a1add3bbc2a1

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsSt
import Theorems.Thm_ReciprocityTheory_AnForm_A_sum_finset_fin_succ
import Theorems.Thm_ReciprocityTheory_AnForm_A_det_single_add
import Theorems.Thm_ReciprocityTheory_AnForm_A_submatrix_finsetSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory ReciprocityTheory.AnForm
noncomputable section
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution {n : ℕ} (B : Fin n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (j : Fin (n + 1)) :
    mdisc (Fin.cons (Matrix.single j j 1) B : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) =
      (1 / ((n + 1 : ℕ) : ℂ)) * mdisc (fun i => (B i).submatrix j.succAbove j.succAbove) := by
  classical
  set X : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := Fin.cons (Matrix.single j j 1) B
    with hX
  have hX0 : X 0 = Matrix.single j j 1 := by simp [X]
  have hXs : ∀ k : Fin n, X k.succ = B k := fun k => by simp [X]
  have core : ∑ S : Finset (Fin (n + 1)), (-1 : ℂ) ^ (n + 1 - S.card) * (∑ k ∈ S, X k).det =
      ∑ S : Finset (Fin n), (-1 : ℂ) ^ (n - S.card) *
        (∑ k ∈ S, (B k).submatrix j.succAbove j.succAbove).det := by
    rw [sum_finset_fin_succ]
    refine Finset.sum_congr rfl fun S _ => ?_
    have h0 : (0 : Fin (n + 1)) ∉ S.map (Fin.succEmb n) := by simp [Fin.succ_ne_zero]
    have hsum : ∑ k ∈ S.map (Fin.succEmb n), X k = ∑ k ∈ S, B k := by
      rw [Finset.sum_map]; exact Finset.sum_congr rfl fun k _ => hXs k
    have hS : S.card ≤ n := by simpa using Finset.card_le_univ S
    have hc : (insert 0 (S.map (Fin.succEmb n))).card = S.card + 1 := by
      rw [Finset.card_insert_of_notMem h0, Finset.card_map]
    rw [Finset.sum_insert h0, hsum, hc, Finset.card_map, hX0, det_single_add,
      submatrix_finsetSum, show n + 1 - S.card = (n - S.card) + 1 by omega,
      show n + 1 - (S.card + 1) = n - S.card by omega, pow_succ]
    ring
  unfold mdisc
  rw [core, Nat.factorial_succ]
  push_cast
  field_simp
end ReciprocityTheory.AnForm.A
