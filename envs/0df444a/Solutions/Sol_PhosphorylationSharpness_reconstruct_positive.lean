-- Prove2me | solution 1 for PhosphorylationSharpness.reconstruct_positive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:24:46.212125+00:00
-- url     : https://prove2.me/submissions/7a835a3f-ba61-4f37-aa54-13c2bee6c852

import Mathlib
import Definitions.Def_proofs_PhosphorylationSharpness_Source

set_option autoImplicit true
open PhosphorylationSharpness
noncomputable section
open scoped BigOperators
namespace PhosphorylationSharpness
theorem _root_.solution {n : ℕ} (t : Fin (n+1) → ℝ) (B D : Fin n → ℝ)
    (ht : ∀ i, 0 < t i) (hB : ∀ i, 0 < B i) (hD : ∀ i, 0 < D i)
    {u s f : ℝ} (hu : 0 < u) (hs : 0 < s) (hf : 0 < f) :
    (reconstruct t B D u s f).Positive := by
  refine ⟨?_, mul_pos hu hf, hf, ?_, ?_⟩
  · intro i
    exact mul_pos (mul_pos (ht _) (pow_pos hu _)) hs
  · intro i
    exact mul_pos (mul_pos (mul_pos (hB _) (pow_pos hu _)) hs) hf
  · intro i
    exact mul_pos (mul_pos (mul_pos (hD _) (pow_pos hu _)) hs) hf
end PhosphorylationSharpness
