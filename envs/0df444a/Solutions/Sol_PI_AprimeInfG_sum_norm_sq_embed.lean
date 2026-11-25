-- Prove2me | solution 1 for PI.AprimeInfG.sum_norm_sq_embed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:36:11.63955+00:00
-- url     : https://prove2.me/submissions/260f71e7-988d-437d-85fd-1b1df82e8cf8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_BlockEmb
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace PI.AprimeInfG
open scoped Matrix
variable {n k : ℕ} {S : Finset (Fin n)}
private theorem emb0_apply_coe_coe (e : Fin k ≃ S) (X : Matrix (Fin k) (Fin k) ℂ) (a b : Fin k) :
    emb0 e X (e a) (e b) = X a b := by
  simp [emb0]
private theorem emb0_apply_of_left_not_mem (e : Fin k ≃ S) (X : Matrix (Fin k) (Fin k) ℂ) {i j : Fin n}
    (hi : i ∉ S) : emb0 e X i j = 0 := by
  simp [emb0, hi]
private theorem emb0_apply_of_right_not_mem (e : Fin k ≃ S) (X : Matrix (Fin k) (Fin k) ℂ) {i j : Fin n}
    (hj : j ∉ S) : emb0 e X i j = 0 := by
  simp [emb0, hj]
private theorem sum_eq_sum_equiv_of_eq_zero_of_not_mem {M : Type*} [AddCommMonoid M] (e : Fin k ≃ S) (F : Fin n → M)
    (hF : ∀ l, l ∉ S → F l = 0) : ∑ l, F l = ∑ c, F (e c) := by
  rw [← Finset.sum_subset (Finset.subset_univ S) (fun l _ hl => hF l hl), ← Finset.sum_coe_sort S]
  exact (Equiv.sum_comp e (fun x : S => F x)).symm
end PI.AprimeInfG
end
end

set_option autoImplicit false
noncomputable section
open PI PI.AprimeInfG
open scoped Matrix
variable {n k : ℕ} {S : Finset (Fin n)}
namespace PI.AprimeInfG
theorem _root_.solution (e : Fin k ≃ S) (X : Matrix (Fin k) (Fin k) ℂ) :
    (∑ i, ∑ j, ‖emb0 e X i j‖ ^ 2) = ∑ a, ∑ b, ‖X a b‖ ^ 2 := by
  rw [sum_eq_sum_equiv_of_eq_zero_of_not_mem e]
  · refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [sum_eq_sum_equiv_of_eq_zero_of_not_mem e]
    · simp only [emb0_apply_coe_coe]
    · intro j hj
      simp [emb0_apply_of_right_not_mem e X hj]
  · intro i hi
    simp [emb0_apply_of_left_not_mem e X hi]
end PI.AprimeInfG
