-- Prove2me | solution 1 for PhosphorylationSharpness.realize_positive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:24:27.883448+00:00
-- url     : https://prove2.me/submissions/6b6505bd-e0de-41d6-b5df-f178c4e8be55

import Mathlib
import Definitions.Def_proofs_PhosphorylationSharpness_Source

set_option autoImplicit true
open PhosphorylationSharpness
noncomputable section
open scoped BigOperators
namespace PhosphorylationSharpness
theorem _root_.solution {n : ℕ} (t : Fin (n+1) → ℝ) (B D : Fin n → ℝ)
    (ht : ∀ i, 0 < t i) (hB : ∀ i, 0 < B i) (hD : ∀ i, 0 < D i) :
    (realize t B D).Positive := by
  intro i
  dsimp [realize]
  exact ⟨div_pos (mul_pos (by norm_num) (hD i)) (ht _), div_pos (hD _) (hB _),
    div_pos (hD _) (hB _), div_pos (mul_pos (by norm_num) (hD i)) (ht _), by norm_num, by norm_num⟩
end PhosphorylationSharpness
