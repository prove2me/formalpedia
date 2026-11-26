-- Prove2me | solution 1 for TunnellMap.quadraticEquation_iff_root_certificate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:52:33.691802+00:00
-- url     : https://prove2.me/submissions/23a58cf8-453f-41bf-8681-af5d3c066861

import Definitions.Def_TunnellMap_ShortInterval
import Definitions.Def_TunnellMap_QuadraticRoots

set_option autoImplicit true
open TunnellMap
namespace TunnellMap
theorem _root_.solution {α c d a : ℤ} (hα : α ≠ 0) :
    quadraticEquation α c d a ↔
      ∃ u : ℤ, u ^ 2 = quadraticHalfDiscriminant α c d ∧ α * a = -c + u := by
  constructor
  · intro h
    refine ⟨α * a + c, ?_, by ring⟩
    unfold quadraticEquation at h
    unfold quadraticHalfDiscriminant
    have hlinear : α * a ^ 2 + 2 * c * a = -d := by linarith
    calc
      (α * a + c) ^ 2 = c ^ 2 + α * (α * a ^ 2 + 2 * c * a) := by ring
      _ = c ^ 2 + α * (-d) := by rw [hlinear]
      _ = c ^ 2 - α * d := by ring
  · rintro ⟨u, hu, ha⟩
    unfold quadraticEquation quadraticHalfDiscriminant at *
    apply mul_left_cancel₀ hα
    calc
      α * (α * a ^ 2 + 2 * c * a + d) =
          (α * a + c) ^ 2 - (c ^ 2 - α * d) := by ring
      _ = u ^ 2 - (c ^ 2 - α * d) := by rw [ha]; ring
      _ = 0 := by rw [hu]; ring
      _ = α * 0 := by ring
end TunnellMap
