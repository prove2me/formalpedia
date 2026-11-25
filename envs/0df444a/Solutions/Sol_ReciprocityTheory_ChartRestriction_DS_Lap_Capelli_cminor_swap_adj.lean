-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.cminor_swap_adj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:26:10.38681+00:00
-- url     : https://prove2.me/submissions/27a0fe47-43b0-4a0a-bb55-1dac08aa6493

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_BasicCycleRangeLastCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_ColAnti
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_capEntry_two
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_prod_ofFn_split_adj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Finset
namespace ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
open ReciprocityTheory.ChartRestriction.DS
variable {𝒰 : Type*} [Ring 𝒰] [Algebra ℂ 𝒰] {n : ℕ} (E : Fin n → Fin n → 𝒰)
private theorem sum_eq_zero_of_add_equiv_apply_eq_zero {M α : Type*} [AddCommGroup M] [Module ℂ M] [Fintype α]
    (e : α ≃ α) (G : α → M) (h : ∀ a, G a + G (e a) = 0) : ∑ a, G a = 0 := by
  have h2 : ∑ a, G a + ∑ a, G (e a) = 0 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero (fun a _ => h a)
  rw [Equiv.sum_comp e G, ← two_smul ℂ] at h2
  have h4 : ((1 / 2 : ℂ) * 2) • ∑ a, G a = 0 := by rw [← smul_smul, h2, smul_zero]
  rwa [show (1 / 2 : ℂ) * 2 = 1 by norm_num, one_smul] at h4
end ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
end
end

set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
open ReciprocityTheory.ChartRestriction.DS
variable {𝒰 : Type*} [Ring 𝒰] [Algebra ℂ 𝒰] {n : ℕ} (E : Fin n → Fin n → 𝒰)
namespace ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
theorem _root_.solution (hE : GlRelR E) {p : ℕ} (R C : Fin (p + 1) → Fin n) (j : Fin p) (x : ℂ) :
    cminor E R (C ∘ Equiv.swap j.castSucc j.succ) x = -cminor E R C x := by
  obtain ⟨τ, hτ⟩ : ∃ τ : Equiv.Perm (Fin (p + 1)), τ = Equiv.swap j.castSucc j.succ := ⟨_, rfl⟩
  rw [← hτ]
  have hab : j.castSucc ≠ j.succ := (Fin.castSucc_lt_succ : j.castSucc < j.succ).ne
  have hτa : τ j.castSucc = j.succ := by rw [hτ]; exact Equiv.swap_apply_left _ _
  have hτb : τ j.succ = j.castSucc := by rw [hτ]; exact Equiv.swap_apply_right _ _
  have hτm : ∀ m, m ≠ j.castSucc → m ≠ j.succ → τ m = m := fun m h1 h2 => by
    rw [hτ]; exact Equiv.swap_apply_of_ne_of_ne h1 h2
  have hsg : ∀ σ : Equiv.Perm (Fin (p + 1)),
      ((Equiv.Perm.sign (σ * τ) : ℤˣ) : ℤ) = -((Equiv.Perm.sign σ : ℤˣ) : ℤ) := by
    intro σ
    rw [Equiv.Perm.sign_mul, hτ, Equiv.Perm.sign_swap hab]
    simp
  have hxb : x - ((j.succ : ℕ) : ℂ) = x - ((j.castSucc : ℕ) : ℂ) - 1 := by
    simp only [Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]; ring
  rw [eq_neg_iff_add_eq_zero]
  unfold cminor
  rw [← Finset.sum_add_distrib]
  apply sum_eq_zero_of_add_equiv_apply_eq_zero (Equiv.mulRight τ)
  intro σ
  simp only [Equiv.coe_mulRight, Equiv.Perm.mul_apply, Function.comp_apply, hsg, neg_smul]
  obtain ⟨P, Q, hPQ⟩ := prod_ofFn_split_adj
    (fun m => capEntry E (x - ((m : ℕ) : ℂ)) (R (σ m)) (C m)) j
  have h1 := hPQ (fun m => capEntry E (x - ((m : ℕ) : ℂ)) (R (σ m)) (C m)) (fun m _ _ => rfl)
  have h2 := hPQ (fun m => capEntry E (x - ((m : ℕ) : ℂ)) (R (σ m)) (C (τ m)))
    (fun m h h' => by simp only [hτm m h h'])
  have h3 := hPQ (fun m => capEntry E (x - ((m : ℕ) : ℂ)) (R (σ (τ m))) (C m))
    (fun m h h' => by simp only [hτm m h h'])
  have h4 := hPQ (fun m => capEntry E (x - ((m : ℕ) : ℂ)) (R (σ (τ m))) (C (τ m)))
    (fun m h h' => by simp only [hτm m h h'])
  simp only [hτa, hτb, hxb] at h1 h2 h3 h4
  rw [h1, h2, h3, h4]
  have hx := eq_neg_iff_add_eq_zero.mp (capEntry_two E hE (R (σ j.castSucc)) (R (σ j.succ))
    (C j.castSucc) (C j.succ) (x - ((j.castSucc : ℕ) : ℂ)))
  have hz := congrArg (fun t => ((Equiv.Perm.sign σ : ℤˣ) : ℤ) • (P * t * Q)) hx
  simp only [mul_zero, zero_mul, smul_zero] at hz
  rw [← hz]
  simp only [mul_add, add_mul, mul_sub, sub_mul, smul_add, smul_sub, mul_assoc]
  abel
end ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
