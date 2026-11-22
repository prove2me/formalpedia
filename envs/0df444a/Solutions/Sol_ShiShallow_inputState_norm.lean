-- Prove2me | solution 1 for ShiShallow.inputState_norm
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-10T04:41:03.617857+00:00
-- url     : https://prove2.me/submissions/516da7ec-4e49-45fd-b689-d3a4c044dec4

/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi

Shallow quantum circuits and causal cones.

MODIFICATIONS made for publication on Prove2me: the enclosing `namespace` is replaced by `section`+`open` and the target theorem is renamed to `solution`;
no statement or proof was otherwise altered.

Built against Mathlib (Apache-2.0) at revision 0df444a360eaa60ab8c11dca51a86af692955474.
-/
import Definitions.Def_ShiShallow_Circuit

section
open ShiShallow

theorem solution {n m : ℕ} (x : Bits n) :
    ∑ y : Bits (n + m), ‖inputState (m := m) x y‖ ^ 2 = 1 := by
  classical
  set y₀ : Bits (n + m) := fun k => Fin.addCases (fun i => x i) (fun _ => false) k with hy₀
  have hP : ∀ y : Bits (n + m),
      ((∀ i : Fin n, y (Fin.castAdd m i) = x i) ∧ (∀ k : Fin m, y (Fin.natAdd n k) = false))
      ↔ y = y₀ := by
    intro y
    constructor
    · rintro ⟨h1, h2⟩
      funext k
      refine Fin.addCases (fun i => ?_) (fun j => ?_) k
      · simpa [hy₀] using h1 i
      · simpa [hy₀] using h2 j
    · rintro rfl
      exact ⟨fun i => by simp [hy₀], fun j => by simp [hy₀]⟩
  have hval : ∀ y : Bits (n + m), ‖inputState (m := m) x y‖ ^ 2 = if y = y₀ then 1 else 0 := by
    intro y
    unfold inputState
    by_cases hy : y = y₀
    · rw [if_pos ((hP y).mpr hy), if_pos hy]; simp
    · rw [if_neg (fun hc => hy ((hP y).mp hc)), if_neg hy]; simp
  simp [hval]

end
