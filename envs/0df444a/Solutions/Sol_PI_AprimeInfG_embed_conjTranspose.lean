-- Prove2me | solution 1 for PI.AprimeInfG.embed_conjTranspose
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:37:28.883202+00:00
-- url     : https://prove2.me/submissions/3bb970a9-ac3c-4e53-8f09-3a19ef22f48a

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
private theorem exists_equiv_coe_eq_of_mem (e : Fin k ≃ S) {i : Fin n} (hi : i ∈ S) :
    ∃ a, (e a : Fin n) = i :=
  ⟨e.symm ⟨i, hi⟩, by simp⟩
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
    emb0 e Xᴴ = (emb0 e X)ᴴ := by
  ext i j
  rw [Matrix.conjTranspose_apply]
  by_cases hi : i ∈ S
  · by_cases hj : j ∈ S
    · obtain ⟨a, rfl⟩ := exists_equiv_coe_eq_of_mem e hi
      obtain ⟨b, rfl⟩ := exists_equiv_coe_eq_of_mem e hj
      rw [emb0_apply_coe_coe, emb0_apply_coe_coe, Matrix.conjTranspose_apply]
    · rw [emb0_apply_of_right_not_mem e _ hj, emb0_apply_of_left_not_mem e _ hj, star_zero]
  · rw [emb0_apply_of_left_not_mem e _ hi, emb0_apply_of_right_not_mem e _ hi, star_zero]
end PI.AprimeInfG
