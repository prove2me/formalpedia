-- Prove2me | solution 1 for ReciprocityTheory.Coh.CCA.hd_hcup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:58:19.030644+00:00
-- url     : https://prove2.me/submissions/f80776f7-6694-47c6-abb6-44050e89fb5f

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupCorA
import Definitions.Def_ReciprocityTheory_GroupCohomology_CupCorB
import Theorems.Thm_ReciprocityTheory_Coh_CCA_val_succAbove
import Theorems.Thm_ReciprocityTheory_Coh_CCA_x_congr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh ReciprocityTheory.Coh.CCA
open ReciprocityTheory.Gal Cx Function
noncomputable section
universe u
variable {R : Type u} [CommRing R] {X V W Z : Type u} [AddCommGroup V] [Module R V]
  [AddCommGroup W] [Module R W] [AddCommGroup Z] [Module R Z]
namespace ReciprocityTheory.Coh.CCA
theorem _root_.solution (β : V →ₗ[R] W →ₗ[R] Z) (p q : ℕ) (F : (Fin (p + 1) → X) → V)
    (F' : (Fin (q + 1) → X) → W) (hF : hd p F = 0) :
    hd (p + q) (hcup β p q F F') = (-1 : ℤ) ^ p • hcup β p (q + 1) F (hd q F') := by
  funext x
  have hF' := congrFun hF (fun k : Fin (p + 2) => x ⟨k, by omega⟩)
  simp only [hd, Pi.zero_apply] at hF'
  rw [Fin.sum_univ_castSucc] at hF'
  have e0 : F (fun j => x ⟨((Fin.last (p + 1)).succAbove j : ℕ), by omega⟩) =
      F (fun i => x ⟨i, by omega⟩) := by
    congr 1; funext k; congr 1; ext; simp [val_succAbove]
  rw [e0] at hF'
  have hsum : ∑ a : Fin (p + 1), (-1 : ℤ) ^ (a : ℕ) •
      F (fun j => x ⟨((Fin.castSucc a).succAbove j : ℕ), by omega⟩) =
      (-1 : ℤ) ^ p • F (fun i => x ⟨i, by omega⟩) := by
    have h2 := eq_neg_of_add_eq_zero_left hF'
    simp only [Fin.val_castSucc, Fin.val_last] at h2
    rw [h2, pow_succ, mul_neg_one, neg_smul, neg_neg]
  have h : p + 1 + (q + 1) = p + q + 2 := by omega
  have key : (∑ a : Fin (p + 1), (-1 : ℤ) ^ (a : ℕ) •
      β (F fun j => x ⟨(a.castSucc.succAbove j : ℕ), by omega⟩) (F' fun j => x ⟨p + 1 + j, by omega⟩)) +
      ∑ b : Fin (q + 1), (-1 : ℤ) ^ (p + 1 + b : ℕ) • β (F fun i => x ⟨i, by omega⟩)
        (F' fun j => x ⟨p + (b.succ.succAbove j : ℕ), by omega⟩) =
      (-1 : ℤ) ^ p • β (F fun i => x ⟨i, by omega⟩)
        ((-1 : ℤ) ^ ((0 : Fin (q + 2)) : ℕ) • F' (fun j => x ⟨p + ((0 : Fin (q + 2)).succAbove j : ℕ), by omega⟩) +
          ∑ b : Fin (q + 1), (-1 : ℤ) ^ (b.succ : ℕ) • F' (fun j => x ⟨p + (b.succ.succAbove j : ℕ), by omega⟩)) := by
    have s1 : (∑ a : Fin (p + 1), (-1 : ℤ) ^ (a : ℕ) •
        β (F fun j => x ⟨(a.castSucc.succAbove j : ℕ), by omega⟩) (F' fun j => x ⟨p + 1 + j, by omega⟩)) =
        β (∑ a : Fin (p + 1), (-1 : ℤ) ^ (a : ℕ) • F fun j => x ⟨(a.castSucc.succAbove j : ℕ), by omega⟩)
          (F' fun j => x ⟨p + 1 + j, by omega⟩) := by
      simp [map_sum, LinearMap.sum_apply]
    have e1 : (F' fun j => x ⟨p + ((0 : Fin (q + 2)).succAbove j : ℕ), by omega⟩) =
        F' fun j => x ⟨p + 1 + j, by omega⟩ := by
      congr 1; funext k; congr 1; ext; simp [val_succAbove]; omega
    rw [s1, hsum, e1]
    simp only [Fin.val_zero, pow_zero, one_smul, map_add, map_sum, map_zsmul, smul_add, Finset.smul_sum,
      smul_smul, Fin.val_succ, LinearMap.smul_apply]
    congr 1
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← pow_add]; congr 2; omega
  rw [Pi.smul_apply]
  unfold hd hcup
  beta_reduce
  conv_lhs => rw [← (finCongr h).sum_comp, Fin.sum_univ_add]
  conv_rhs => rw [Fin.sum_univ_succ]
  convert key using 4
  all_goals first
    | (simp; done)
    | (congr 2 <;> (try funext k) <;> (try congr 1) <;> (try funext k) <;> (first | apply x_congr | apply Fin.ext) <;>
        simp only [val_succAbove, finCongr_apply, Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd,
          Fin.val_castSucc, Fin.val_succ] <;> (try split_ifs) <;>
        (try simp only [finCongr_apply, Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd,
          Fin.val_castSucc, Fin.val_succ] at *) <;> omega)
end ReciprocityTheory.Coh.CCA
