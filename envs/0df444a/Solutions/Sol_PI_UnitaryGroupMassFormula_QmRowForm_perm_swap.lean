-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QmRowForm.perm_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:52:24.170018+00:00
-- url     : https://prove2.me/submissions/766da81e-3803-4000-bce5-2e9129fe4e9f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RowFormPermutationSplit_Development
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RowFormPermutationSplit_PermutedRowProductSplit
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmRowForm_dblAlt_eq
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmRowForm_perm_Tm_comm
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmRowForm_perm_fix
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmRowForm_perm_split_swap
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
theorem _root_.solution {A : Type*} [Ring A] [Algebra ℂ A] {n m : ℕ} (E : Fin n → Fin n → A) (hE : GlRel E)
    (a b : Fin (m + 1) → Fin n) (x : Fin (m + 1) → ℂ) (i : Fin m) :
    doubleRowFormSum E a b (x ∘ Equiv.swap i.castSucc i.succ) = doubleRowFormSum E a b x := by
  set s := Equiv.swap i.castSucc i.succ with hs
  have hu : ((Equiv.Perm.sign s : ℤ) * (Equiv.Perm.sign s : ℤ)) = 1 := by
    rw [← Units.val_mul, Int.units_mul_self, Units.val_one]
  have hε : ∀ σ τ : Equiv.Perm (Fin (m + 1)), (pε (σ * s) (τ * s) : A) = pε σ τ := by
    intro σ τ
    unfold pε
    congr 1
    rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_mul, Units.val_mul, Units.val_mul]
    linear_combination ((Equiv.Perm.sign σ : ℤ) * (Equiv.Perm.sign τ : ℤ)) * hu
  have hagree : ∀ σ τ : Equiv.Perm (Fin (m + 1)), ∀ k : Fin (m + 1), (k : ℕ) ≠ i →
      (k : ℕ) ≠ (i : ℕ) + 1 → pF E a b x (σ * s) (τ * s) k = pF E a b x σ τ k := by
    intro σ τ k h1 h2
    simp only [pF, Equiv.Perm.mul_apply, hs, perm_fix i k h1 h2]
  have hL : ∀ σ τ, pL E a b x i (σ * s) (τ * s) = pL E a b x i σ τ := by
    intro σ τ
    unfold pL
    rw [(ofFn_take_drop_eq_of_eq_off_pair _ _ i (hagree σ τ)).1]
  have hR : ∀ σ τ, pR E a b x i (σ * s) (τ * s) = pR E a b x i σ τ := by
    intro σ τ
    unfold pR
    rw [(ofFn_take_drop_eq_of_eq_off_pair _ _ i (hagree σ τ)).2]
  have hX : ∀ σ τ, permutedRowProductSplitSum E a b i (σ * s) (τ * s) = permutedRowProductSplit E a b i σ τ := by
    intro σ τ
    simp only [permutedRowProductSplitSum, permutedRowProductSplit, Equiv.Perm.mul_apply, hs, Equiv.swap_apply_left, Equiv.swap_apply_right]
  have h1 : doubleRowFormSum E a b (x ∘ s) =
      ∑ σ, ∑ τ, pε σ τ * (List.ofFn (pF E a b x σ τ ∘ s)).prod := by
    rw [dblAlt_eq, ← Equiv.sum_comp (Equiv.mulRight s)]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [← Equiv.sum_comp (Equiv.mulRight s)]
    refine Finset.sum_congr rfl fun τ _ => ?_
    simp only [Equiv.coe_mulRight]
    rw [hε]
    rfl
  have h2 : ∀ σ τ, (List.ofFn (pF E a b x σ τ)).prod - (List.ofFn (pF E a b x σ τ ∘ s)).prod =
      pL E a b x i σ τ * (permutedRowProductSplitSum E a b i σ τ - permutedRowProductSplit E a b i σ τ) * pR E a b x i σ τ := by
    intro σ τ
    rw [hs, perm_split_swap]
    unfold pL pR
    congr 2
    simp only [pF]
    rw [perm_Tm_comm, hE]
    rfl
  have h3 : ∑ σ, ∑ τ, pε σ τ * (pL E a b x i σ τ * permutedRowProductSplitSum E a b i σ τ * pR E a b x i σ τ) =
      ∑ σ, ∑ τ, pε σ τ * (pL E a b x i σ τ * permutedRowProductSplit E a b i σ τ * pR E a b x i σ τ) := by
    rw [← Equiv.sum_comp (Equiv.mulRight s)]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [← Equiv.sum_comp (Equiv.mulRight s)]
    refine Finset.sum_congr rfl fun τ _ => ?_
    simp only [Equiv.coe_mulRight]
    rw [hε, hL, hR, hX]
  rw [h1, dblAlt_eq]
  symm
  rw [← sub_eq_zero]
  calc (∑ σ, ∑ τ, pε σ τ * (List.ofFn (pF E a b x σ τ)).prod) -
        ∑ σ, ∑ τ, pε σ τ * (List.ofFn (pF E a b x σ τ ∘ s)).prod
      = ∑ σ, ∑ τ, (pε σ τ * (pL E a b x i σ τ * permutedRowProductSplitSum E a b i σ τ * pR E a b x i σ τ) -
          pε σ τ * (pL E a b x i σ τ * permutedRowProductSplit E a b i σ τ * pR E a b x i σ τ)) := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun τ _ => ?_
        rw [← mul_sub, h2]
        noncomm_ring
    _ = 0 := by
        simp only [Finset.sum_sub_distrib]
        rw [h3, sub_self]
end PI.UnitaryGroupMassFormula.QmRowForm
