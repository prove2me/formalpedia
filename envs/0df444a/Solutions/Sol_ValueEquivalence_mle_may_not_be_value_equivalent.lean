-- Prove2me | solution 1 for ValueEquivalence.mle_may_not_be_value_equivalent
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-24T07:12:34.37664+00:00
-- url     : https://prove2.me/submissions/bf9b71a3-2b15-4f81-85a2-772ac52df636

import Mathlib
import Definitions.Def_ValueEquivalence_Basic

namespace ValueEquivalence

/-- the true kernel: uniform on states `1` and `2` -/
noncomputable def ve3_pstar : Fin 3 → Fin 1 → Fin 3 → ℝ := fun _ _ s' => if s' = 0 then 0 else 1 / 2

/-- a kernel that is not value equivalent but has finite loss -/
noncomputable def ve3_P1 : Fin 3 → Fin 1 → Fin 3 → ℝ :=
  fun _ _ s' => if s' = 0 then 0 else if s' = 1 then 2 / 3 else 1 / 3

/-- a value-equivalent kernel with infinite loss -/
def ve3_P2 : Fin 3 → Fin 1 → Fin 3 → ℝ := fun _ _ s' => if s' = 0 then 1 else 0

def ve3_v : Fin 3 → ℝ := fun s => if s = 0 then 0 else if s = 1 then 1 else -1

def ve3_D : Fin 3 → Fin 1 → ℝ := fun s _ => if s = 0 then 1 else 0

lemma ve3_pstar_kernel : IsTransitionKernel ve3_pstar := by
  refine ⟨fun s a s' => ?_, fun s a => ?_⟩
  · unfold ve3_pstar; split_ifs <;> norm_num
  · simp [ve3_pstar, Fin.sum_univ_three]; norm_num

lemma ve3_P1_kernel : IsTransitionKernel ve3_P1 := by
  refine ⟨fun s a s' => ?_, fun s a => ?_⟩
  · unfold ve3_P1; split_ifs <;> norm_num
  · simp [ve3_P1, Fin.sum_univ_three]; norm_num

lemma ve3_P2_kernel : IsTransitionKernel ve3_P2 := by
  refine ⟨fun s a s' => ?_, fun s a => ?_⟩
  · unfold ve3_P2; split_ifs <;> norm_num
  · simp [ve3_P2]

noncomputable def ve3_mstar : Model (Fin 3) (Fin 1) := ⟨fun _ _ => 0, ve3_pstar, ve3_pstar_kernel⟩

lemma ve3_loss_P2 : mleLoss ve3_D ve3_pstar ve3_P2 = ⊤ := by
  simp [mleLoss, klDivFin, ve3_D, ve3_pstar, ve3_P2, Fin.sum_univ_three]

lemma ve3_loss_P1 : mleLoss ve3_D ve3_pstar ve3_P1 ≠ ⊤ := by
  simp [mleLoss, klDivFin, ve3_D, ve3_pstar, ve3_P1, Fin.sum_univ_three]
  rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
  exact EReal.coe_ne_top _

end ValueEquivalence


open ValueEquivalence in
theorem solution :
    ∃ (nS nA : ℕ) (γ : ℝ) (mstar : Model (Fin nS) (Fin nA))
      (PP : Set (Fin nS → Fin nA → Fin nS → ℝ)) (Pol : Set (Fin nS → Fin nA → ℝ))
      (V : Set (Fin nS → ℝ)) (D : Fin nS → Fin nA → ℝ),
      0 ≤ γ ∧ γ < 1 ∧ Pol ⊆ policies ∧ (∀ P ∈ PP, IsTransitionKernel P) ∧
      (∀ s a, 0 ≤ D s a) ∧ ∑ s, ∑ a, D s a = 1 ∧
      (veKernels γ mstar PP Pol V).Nonempty ∧
      (∃ P ∈ PP, ∀ P' ∈ PP, mleLoss D mstar.p P ≤ mleLoss D mstar.p P') ∧
      ∀ P ∈ PP, (∀ P' ∈ PP, mleLoss D mstar.p P ≤ mleLoss D mstar.p P') →
        P ∉ veKernels γ mstar PP Pol V := by
  refine ⟨3, 1, 1 / 2, ve3_mstar, {ve3_P1, ve3_P2}, {fun _ _ => 1}, {ve3_v}, ve3_D,
    by norm_num, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro π rfl
    exact ⟨fun _ _ => zero_le_one, fun s => by simp⟩
  · rintro P (rfl | rfl)
    · exact ve3_P1_kernel
    · exact ve3_P2_kernel
  · intro s a
    unfold ve3_D; split_ifs <;> norm_num
  · simp [ve3_D]
  · refine ⟨ve3_P2, ⟨⟨fun _ _ => 0, ve3_P2, ve3_P2_kernel⟩, ⟨⟨rfl, by simp⟩, ?_⟩, rfl⟩⟩
    rintro π rfl v rfl
    funext s
    simp [bellman, ve3_mstar, ve3_pstar, ve3_P2, ve3_v, Fin.sum_univ_three]
  · refine ⟨ve3_P1, by simp, ?_⟩
    rintro P' (rfl | rfl)
    · exact le_rfl
    · change _ ≤ mleLoss ve3_D ve3_pstar ve3_P2
      rw [ve3_loss_P2]
      exact le_top
  · rintro P (rfl | rfl) hmin hmem
    · obtain ⟨m, ⟨⟨hr, -⟩, hve⟩, hp⟩ := hmem
      have h := congrFun (hve (fun _ _ => 1) rfl ve3_v rfl) 0
      simp only [bellman, hr, hp] at h
      simp [ve3_mstar, ve3_pstar, ve3_P1, ve3_v, Fin.sum_univ_three] at h
      norm_num at h
    · have h := hmin ve3_P1 (by simp)
      change mleLoss ve3_D ve3_pstar ve3_P2 ≤ mleLoss ve3_D ve3_pstar ve3_P1 at h
      rw [ve3_loss_P2, top_le_iff] at h
      exact ve3_loss_P1 h
