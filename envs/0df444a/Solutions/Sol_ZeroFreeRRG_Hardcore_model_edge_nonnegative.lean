-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.model_edge_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:02:12.189283+00:00
-- url     : https://prove2.me/submissions/b888a718-f1ea-4713-a5d1-9743db6648da

import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional
import Mathlib
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem solution (m : Model) (hm : m.Valid) (t : ℝ) (ht : m.PosParam t) :
    ∀ a b, 0 ≤ m.P t a b := by
  cases m with
  | hardcore =>
    change 0 < t ∧ t < 1/2 at ht
    intro a b
    change Fin 2 at a b
    fin_cases a <;> fin_cases b <;> simp [Model.P,Model.Spin] <;> linarith
  | potts q =>
    change 2 ≤ q at hm
    change 0 < t ∧ t < 1 at ht
    have hq : (2:ℝ) ≤ q := by exact_mod_cast hm
    have hq0 : 0 < (q:ℝ) := by linarith
    have hq1 : 0 < (q:ℝ)-1+t := by linarith
    have hden : 0 < (q:ℝ)*((q:ℝ)-1+t) := mul_pos hq0 hq1
    intro a b
    change Fin q at a b
    change 0 ≤ ((1:ℝ) + if a=b then t-1 else 0) / ((q:ℝ)*((q:ℝ)-1+t))
    apply div_nonneg _ hden.le
    by_cases h : a=b <;> simp [h] <;> linarith
