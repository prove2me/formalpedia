-- Prove2me | solution 1 for RobustPower.CostGap.robust_value_ge_one
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:21:16.301932+00:00
-- url     : https://prove2.me/submissions/47fa2f9d-b5f4-4e16-b4a6-cbd9035a84f6

import Mathlib
import Definitions.Def_RobustPower_CostGap_Problems

set_option autoImplicit false
open MeasureTheory Matrix RobustPower.CostGap

theorem solution {n : ℕ} (hn : 0 < n) {Ω : Type*}
    (d : Ω → Fin n → ℝ) (hrange : Set.range d = Set.Icc 0 1) :
    (1 : EReal) ≤
      zRobBD (0 : Matrix (Fin 1) (Fin 0) ℝ) (fun _ _ => 1 : Matrix (Fin 1) (Fin n) ℝ)
          (fun _ _ => 1 : Ω → Fin 1 → ℝ) (0 : Fin 0 → ℝ) d ∅ ∅ := by
  obtain ⟨ω0, hω0⟩ : ∃ ω0, d ω0 = fun _ => (1 : ℝ) := by
    have : (fun _ : Fin n => (1 : ℝ)) ∈ Set.range d := by
      rw [hrange]; exact ⟨fun _ => zero_le_one, le_refl _⟩
    exact this
  unfold zRobBD
  refine le_iInf fun x => le_iInf fun y => le_iInf fun hf => ?_
  have h1 : (1 : ℝ) ≤ ∑ j, y j := by
    have := hf.2.2 ω0 0
    simpa [Matrix.mulVec, dotProduct] using this
  have hc : ((0 : Fin 0 → ℝ) ⬝ᵥ x) = 0 := by simp
  rw [hc]
  calc (1 : EReal) ≤ ((∑ j, y j : ℝ) : EReal) := by exact_mod_cast h1
    _ = ((0 : ℝ) : EReal) + ((d ω0 ⬝ᵥ y : ℝ) : EReal) := by
        rw [hω0]; simp [dotProduct]
    _ ≤ ((0 : ℝ) : EReal) + ⨆ ω, ((d ω ⬝ᵥ y : ℝ) : EReal) :=
        add_le_add le_rfl (le_iSup (fun ω => ((d ω ⬝ᵥ y : ℝ) : EReal)) ω0)
