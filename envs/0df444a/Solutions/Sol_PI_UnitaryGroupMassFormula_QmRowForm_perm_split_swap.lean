-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QmRowForm.perm_split_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:42:21.818833+00:00
-- url     : https://prove2.me/submissions/ef917d86-b831-4e7a-a231-98cc0e10b205

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RowFormPermutationSplit_Development
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RowFormPermutationSplit_PermutedRowProductSplit
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmRowForm_perm_fix
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset Formalism.REAL
noncomputable section
namespace PI.UnitaryGroupMassFormula.QmRowForm
private lemma sum_cf_mul_sum_cf_mul_eq_sum_sum_toReal_mul {A : Type*} [Ring A] {m : ℕ} (F : Fin (m + 1) → A) (i : Fin m) :
    (List.ofFn F).prod = ((List.ofFn F).take (i : ℕ)).prod * (F i.castSucc * F i.succ) *
      ((List.ofFn F).drop ((i : ℕ) + 2)).prod := by
  have h0 : (i : ℕ) < (List.ofFn F).length := by simp <;> omega
  have h1 : (i : ℕ) + 1 < (List.ofFn F).length := by simp <;> omega
  conv_lhs => rw [← List.take_append_drop (i : ℕ) (List.ofFn F)]
  rw [List.drop_eq_getElem_cons h0, List.drop_eq_getElem_cons h1]
  simp only [List.prod_append, List.prod_cons, List.getElem_ofFn, mul_assoc]
  rfl
private lemma ofFn_take_drop_eq_of_eq_off_pair {A : Type*} {m : ℕ} (F G : Fin (m + 1) → A) (i : Fin m)
    (h : ∀ k : Fin (m + 1), (k : ℕ) ≠ i → (k : ℕ) ≠ (i : ℕ) + 1 → F k = G k) :
    (List.ofFn F).take (i : ℕ) = (List.ofFn G).take (i : ℕ) ∧
      (List.ofFn F).drop ((i : ℕ) + 2) = (List.ofFn G).drop ((i : ℕ) + 2) := by
  constructor
  · apply List.ext_getElem (by simp)
    intro j hj1 hj2
    simp only [List.getElem_take, List.getElem_ofFn]
    apply h <;> simp at hj1 ⊢ <;> omega
  · apply List.ext_getElem (by simp)
    intro j hj1 hj2
    simp only [List.getElem_drop, List.getElem_ofFn]
    apply h <;> simp <;> omega
end PI.UnitaryGroupMassFormula.QmRowForm
end
end

set_option autoImplicit false
open Finset Formalism.REAL
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.QmRowForm
namespace PI.UnitaryGroupMassFormula.QmRowForm
theorem _root_.solution {A : Type*} [Ring A] {m : ℕ} (F : Fin (m + 1) → A) (i : Fin m) :
    (List.ofFn F).prod - (List.ofFn (F ∘ Equiv.swap i.castSucc i.succ)).prod =
      ((List.ofFn F).take (i : ℕ)).prod * (F i.castSucc * F i.succ - F i.succ * F i.castSucc) *
        ((List.ofFn F).drop ((i : ℕ) + 2)).prod := by
  rw [sum_cf_mul_sum_cf_mul_eq_sum_sum_toReal_mul F i, sum_cf_mul_sum_cf_mul_eq_sum_sum_toReal_mul (F ∘ Equiv.swap i.castSucc i.succ) i]
  obtain ⟨ht, hd⟩ := ofFn_take_drop_eq_of_eq_off_pair (F ∘ Equiv.swap i.castSucc i.succ) F i
    (fun k h1 h2 => by simp [perm_fix i k h1 h2])
  rw [ht, hd]
  simp only [Function.comp, Equiv.swap_apply_left, Equiv.swap_apply_right]
  noncomm_ring
end PI.UnitaryGroupMassFormula.QmRowForm
