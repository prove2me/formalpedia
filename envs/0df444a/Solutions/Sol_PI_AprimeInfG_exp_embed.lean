-- Prove2me | solution 1 for PI.AprimeInfG.exp_embed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:36:47.491798+00:00
-- url     : https://prove2.me/submissions/ba666695-c3fd-469b-8cf4-eadbe5bf57da

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_BlockEmb
import Theorems.Thm_PI_AprimeInfG_embed_pow_succ
import Theorems.Thm_PI_AprimeInfG_continuous_embed
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
private theorem emb0Add_apply (e : Fin k ≃ S) (X : Matrix (Fin k) (Fin k) ℂ) :
    blockEmbeddingAddHom e X = emb0 e X :=
  rfl
private theorem emb0_smul (e : Fin k ≃ S) (c : ℂ) (X : Matrix (Fin k) (Fin k) ℂ) :
    emb0 e (c • X) = c • emb0 e X := by
  ext i j
  rw [Matrix.smul_apply]
  by_cases hi : i ∈ S
  · by_cases hj : j ∈ S
    · obtain ⟨a, rfl⟩ := exists_equiv_coe_eq_of_mem e hi
      obtain ⟨b, rfl⟩ := exists_equiv_coe_eq_of_mem e hj
      rw [emb0_apply_coe_coe, emb0_apply_coe_coe, Matrix.smul_apply]
    · rw [emb0_apply_of_right_not_mem e _ hj, emb0_apply_of_right_not_mem e _ hj, smul_zero]
  · rw [emb0_apply_of_left_not_mem e _ hi, emb0_apply_of_left_not_mem e _ hi, smul_zero]
end PI.AprimeInfG
end
end

set_option autoImplicit false
noncomputable section
open PI PI.AprimeInfG
open scoped Matrix
variable {n k : ℕ} {S : Finset (Fin n)}
set_option backward.isDefEq.respectTransparency false
namespace PI.AprimeInfG
theorem _root_.solution (e : Fin k ≃ S) (X : Matrix (Fin k) (Fin k) ℂ) :
    NormedSpace.exp (emb0 e X) = emb0 e (NormedSpace.exp X) + (1 - emb0 e 1) := by
  letI : NormedRing (Matrix (Fin k) (Fin k) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix (Fin k) (Fin k) ℂ) := Matrix.linftyOpNormedAlgebra
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  have h1 := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) X
  have h2 := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (emb0 e X)
  have h3 := (h1.map (blockEmbeddingAddHom e) (continuous_embed e)).add
    (hasSum_ite_eq 0 (1 - emb0 e 1))
  refine h2.unique ?_
  convert h3 using 1
  all_goals try rfl
  funext m
  rcases m with _ | m
  · simp [emb0Add_apply]
  · simp [emb0Add_apply, emb0_smul, embed_pow_succ]
end PI.AprimeInfG
