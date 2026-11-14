-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.hardcore_vertex_centered
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T08:20:16.523515+00:00
-- url     : https://prove2.me/submissions/e6e4eebd-a473-4f24-9725-630a87aec5ed

import Theorems.Thm_ZeroFreeRRG_Hardcore_hardcore_centered_factors
import Mathlib
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem solution (d : ℕ) (α : ℝ) (ha : 0 < α) (ha1 : α < 1/2)
    (xs : Fin d → Fin 2 → ℝ) (hs : ∀ i, ∑ a, xs i a = 1) :
    let θ := α/(1-α)
    let h := fun i => (xs i 1-α)/(1-α)
    vertexFactor .hardcore α d xs =
      ((∏ i, (1+θ*h i)) + θ*(∏ i, (1-h i)))/(1+θ) := by
  dsimp only
  have hf0 (i : Fin d) : Mmul .hardcore α (xs i) (0 : Fin 2) =
      1+(α/(1-α))*((xs i 1-α)/(1-α)) :=
    (hardcore_centered_factors α ha ha1 (xs i) (xs i) (hs i) (hs i)).1
  have hf1 (i : Fin d) : Mmul .hardcore α (xs i) (1 : Fin 2) =
      1-(xs i 1-α)/(1-α) :=
    (hardcore_centered_factors α ha ha1 (xs i) (xs i) (hs i) (hs i)).2.1
  have hp0 : Model.pi .hardcore α (0 : Fin 2) = 1-α := by
    simp [Model.pi,Model.Spin,Model.P,Fin.sum_univ_two] <;> ring
  have hp1 : Model.pi .hardcore α (1 : Fin 2) = α := by
    simp [Model.pi,Model.Spin,Model.P,Fin.sum_univ_two] <;> ring
  unfold vertexFactor
  change (∑ a : Fin 2, Model.pi .hardcore α a * ∏ i, Mmul .hardcore α (xs i) a) = _
  rw [Fin.sum_univ_two,hp0,hp1]
  simp_rw [hf0,hf1]
  have hden : 1-α ≠ 0 := by linarith
  have hden' : 1+α/(1-α) ≠ 0 := by
    have hh : 0 < 1-α := by linarith
    positivity
  field_simp
  <;> ring
