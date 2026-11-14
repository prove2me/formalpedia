-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.model_has_safe_spin
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T11:07:55.808912+00:00
-- url     : https://prove2.me/submissions/ead78550-1054-4b34-b123-a9fd2b9fe321

import Theorems.Thm_ZeroFreeRRG_Hardcore_model_pi_positive_simplex
import Mathlib
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem solution (m : Model) (hm : m.Valid) (t : ℝ) (ht : m.PosParam t) :
    ∃ a₀ : m.Spin, ∀ a : m.Spin, 0 < m.M t a₀ a := by
  have hπ : ∀ a, 0 < m.pi t a := (model_pi_positive_simplex m hm t ht).1
  have hP : ∃ a₀ : m.Spin, ∀ a : m.Spin, 0 < m.P t a₀ a := by
    cases m with
    | hardcore =>
      change 0 < t ∧ t < 1/2 at ht
      refine ⟨(0 : Fin 2),?_⟩
      intro a
      change Fin 2 at a
      fin_cases a <;> simp [Model.P] <;> linarith
    | potts q =>
      change 2 ≤ q at hm
      change 0 < t ∧ t < 1 at ht
      have hq : (2:ℝ) ≤ q := by exact_mod_cast hm
      have hq0 : 0 < (q:ℝ) := by linarith
      have hq1 : 0 < (q:ℝ)-1+t := by linarith
      refine ⟨⟨0,by omega⟩,?_⟩
      intro a
      change Fin q at a
      change 0 < ((1:ℝ) + if (⟨0,by omega⟩ : Fin q)=a then t-1 else 0) /
        ((q:ℝ)*((q:ℝ)-1+t))
      apply div_pos _ (mul_pos hq0 hq1)
      split_ifs <;> linarith
  obtain ⟨a₀,ha⟩ := hP
  exact ⟨a₀,fun a => div_pos (ha a) (mul_pos (hπ a₀) (hπ a))⟩
