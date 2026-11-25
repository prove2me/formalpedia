-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_InertHeis_Heisenberg__9b2968164a68
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:27:28.605598+00:00
-- url     : https://prove2.me/submissions/885d158b-499d-4e58-b487-3009c8e213d6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_HeisenbergMatrixFacts
import Theorems.Thm_GlobalTheory_CompanionTheory_InertHeis_rowOf_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_InertHeis_colOf_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_InertHeis_cornerOf_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_InertHeis_row_eq
import Theorems.Thm_GlobalTheory_CompanionTheory_InertHeis_corner_eq
import Theorems.Thm_GlobalTheory_CompanionTheory_InertHeis_mem_KU_rad
import Theorems.Thm_GlobalTheory_CompanionTheory_InertHeis_heis_00
import Theorems.Thm_GlobalTheory_CompanionTheory_InertHeis_heis_0m
import Theorems.Thm_GlobalTheory_CompanionTheory_InertHeis_heis_0l
import Theorems.Thm_GlobalTheory_CompanionTheory_InertHeis_heisenberg_middle_first_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_InertHeis_heis_mm
import Theorems.Thm_GlobalTheory_CompanionTheory_InertHeis_heisenberg_last_first_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_InertHeis_heis_lm
import Theorems.Thm_GlobalTheory_CompanionTheory_InertHeis_heis_ll
import Theorems.Thm_GlobalTheory_CompanionTheory_InertHeis_one_mid_mid
import Theorems.Thm_GlobalTheory_CompanionTheory_InertHeis_heis_unitary
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_InertZeta_blk_last
import Theorems.Thm_GlobalTheory_InertZeta_blk_mid
import Theorems.Thm_GlobalTheory_InertZeta_blk_zero
import Theorems.Thm_GlobalTheory_InertZeta_idx_cases
import Theorems.Thm_GlobalTheory_InertZeta_last_ne_zero
import Theorems.Thm_GlobalTheory_InertZeta_mid_ne_last
import Theorems.Thm_GlobalTheory_InertZeta_mid_ne_zero
import Theorems.Thm_GlobalTheory_InertZeta_val_mid
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] GlobalTheory.Doubling.flatSec_self
attribute [local simp] GlobalTheory.Doubling.val_aOf
attribute [local simp] GlobalTheory.Doubling.val_leviOf
attribute [local simp] GlobalTheory.InertZeta.blk_last
attribute [local simp] GlobalTheory.InertZeta.blk_mid
attribute [local simp] GlobalTheory.InertZeta.blk_zero
attribute [local simp] GlobalTheory.InertZeta.val_mid


section
noncomputable section
open Formalism.UG Matrix GlobalTheory.SatakeWeyl GlobalTheory.InertZeta
namespace GlobalTheory.CompanionTheory.InertHeis
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {N : ℕ}
section Entries
variable {u : GU σ (N + 2)}
end Entries
private theorem antiJ_apply_eq_ite_rev {n : ℕ} (i j : Fin n) :
    antiJ L n i j = if j = i.rev then 1 else 0 := by
  have hi := i.isLt
  have hj := j.isLt
  show (if (i : ℕ) + j + 1 = n then (1 : L) else 0) = _
  by_cases h : j = i.rev
  · rw [if_pos h, if_pos]
    subst h
    rw [Fin.val_rev]
    omega
  · rw [if_neg h, if_neg]
    intro h'
    apply h
    ext
    rw [Fin.val_rev]
    omega
private theorem antiJ_mul_apply_eq_apply_rev_left {n : ℕ} (X : Matrix (Fin n) (Fin n) L) (a c : Fin n) :
    (antiJ L n * X) a c = X a.rev c := by
  rw [Matrix.mul_apply]
  simp only [antiJ_apply_eq_ite_rev, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
private theorem antiJ_mul_antiJ_eq_one {n : ℕ} : antiJ L n * antiJ L n = 1 := by
  ext i j
  rw [antiJ_mul_apply_eq_apply_rev_left, antiJ_apply_eq_ite_rev, Fin.rev_rev]
  by_cases h : i = j
  · subst h
    rw [if_pos rfl, Matrix.one_apply_eq]
  · rw [if_neg (Ne.symm h), Matrix.one_apply_ne h]
section Values
variable (r b : Fin N → L) (c : L)
end Values
end GlobalTheory.CompanionTheory.InertHeis
end
end

set_option autoImplicit false
noncomputable section
open Formalism.UG Matrix GlobalTheory.SatakeWeyl GlobalTheory.InertZeta
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertHeis
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {N : ℕ}
namespace GlobalTheory.CompanionTheory.InertHeis
theorem _root_.solution : Heis := by
  intro L _ _ ϖ σ q N hI
  obtain ⟨hσσ, hσ, -⟩ := hI
  refine ⟨fun u hu => ⟨row_eq hu, corner_eq hu, mem_KU_rad hσσ hσ hu⟩,
    fun u hu u' hu' => ⟨rowOf_mul hu hu', colOf_mul hu hu', cornerOf_mul hu hu'⟩, ?_⟩
  intro r c hc
  have hU := heis_unitary hσσ r (fun i => -σ (r i.rev)) c (fun i => rfl) hc
  have hl : (antiJ L (N + 2) * cT σ (heisMat r (fun i => -σ (r i.rev)) c) * antiJ L (N + 2)) *
      heisMat r (fun i => -σ (r i.rev)) c = 1 := by
    have hU' : cT σ (heisMat r (fun i => -σ (r i.rev)) c) * (antiJ L (N + 2) *
        heisMat r (fun i => -σ (r i.rev)) c) = antiJ L (N + 2) := by
      rw [← Matrix.mul_assoc, hU]
    simp only [Matrix.mul_assoc]
    rw [hU', antiJ_mul_antiJ_eq_one]
  have hr := mul_eq_one_comm.mp hl
  refine ⟨⟨⟨heisMat r (fun i => -σ (r i.rev)) c, _, hr, hl⟩, hU⟩, ?_, ?_, ?_⟩
  · intro i j hij
    show heisMat r (fun i => -σ (r i.rev)) c i j = (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) i j
    rcases idx_cases i with rfl | ⟨p, rfl⟩ | rfl <;> rcases idx_cases j with rfl | ⟨q, rfl⟩ | rfl
    · rw [heis_00, Matrix.one_apply_eq]
    · rw [blk_mid, blk_zero] at hij; omega
    · rw [blk_last, blk_zero] at hij; omega
    · rw [heisenberg_middle_first_zero, Matrix.one_apply_ne (mid_ne_zero p)]
    · rw [heis_mm, one_mid_mid]
    · rw [blk_last, blk_mid] at hij; omega
    · rw [heisenberg_last_first_zero, Matrix.one_apply_ne last_ne_zero]
    · rw [heis_lm, Matrix.one_apply_ne (mid_ne_last q).symm]
    · rw [heis_ll, Matrix.one_apply_eq]
  · funext j
    exact heis_0m r _ c j
  · exact heis_0l r _ c
end GlobalTheory.CompanionTheory.InertHeis
