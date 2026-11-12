-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P33.fockSubstitution
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-12T01:04:01.545345+00:00
-- url     : https://prove2.me/submissions/79b70173-c6c6-4864-ba14-511c71fa4733

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P33

noncomputable section

open scoped BigOperators ENNReal

open QAlgorithms.RealRegisters (Hilbert)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

namespace Aux_fockSubstitution

open QAlgorithms.Papers.Independent.Intakethird100.P33

theorem occ_inj {n : ℕ} (w v : Fin n → Fin 3)
    (h : sourceOccupation w = sourceOccupation v) : w = v := by
  funext k
  have h0 := congrFun h (k, false)
  have h1 := congrFun h (k, true)
  unfold sourceOccupation at h0 h1
  obtain ⟨a, ha⟩ : ∃ a, w k = a := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, v k = b := ⟨_, rfl⟩
  simp only [ha, hb] at h0 h1 ⊢
  fin_cases a <;> fin_cases b <;> simp_all

end Aux_fockSubstitution

open QAlgorithms.Papers.Independent.Intakethird100.P33 in
theorem solution (n : ℕ) :
    (∀ w : Fin n → Fin 3, ‖substitutedWord w‖ = 1) ∧
    (∀ w v : Fin n → Fin 3,
      inner ℂ (substitutedWord w) (substitutedWord v) = if w = v then 1 else 0) := by
  have hnorm : ∀ w : Fin n → Fin 3, ‖substitutedWord w‖ = 1 := by
    intro w
    unfold substitutedWord
    rw [lp.norm_single (show (0:ℝ≥0∞) < 2 by norm_num), norm_one]
  refine ⟨hnorm, ?_⟩
  intro w v
  by_cases hwv : w = v
  · subst hwv
    rw [if_pos rfl, inner_self_eq_norm_sq_to_K, hnorm]
    simp
  · rw [if_neg hwv]
    have hne : sourceOccupation w ≠ sourceOccupation v :=
      fun h => hwv (Aux_fockSubstitution.occ_inj w v h)
    unfold substitutedWord
    rw [lp.inner_single_left, lp.single_apply_ne 2 _ _ hne]
    simp

end
