-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.model_interaction_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T11:07:56.49058+00:00
-- url     : https://prove2.me/submissions/abedaaed-fe4b-4f35-97fe-ff4534e020b5

import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional
import Mathlib
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem solution (m : Model) (t : ℝ) : ∀ a b, m.M t a b = m.M t b a := by
  intro a b
  have hP : m.P t a b = m.P t b a := by
    cases m with
    | hardcore =>
      change Fin 2 at a b
      fin_cases a <;> fin_cases b <;> simp [Model.P]
    | potts q =>
      change Fin q at a b
      change ((1:ℝ) + (if a=b then t-1 else 0))/((q:ℝ)*((q:ℝ)-1+t)) =
        ((1:ℝ) + (if b=a then t-1 else 0))/((q:ℝ)*((q:ℝ)-1+t))
      by_cases h : a=b
      · subst b
        simp
      · have h' : b≠a := Ne.symm h
        simp [h,h']
  unfold Model.M
  rw [hP,mul_comm (m.pi t a) (m.pi t b)]
