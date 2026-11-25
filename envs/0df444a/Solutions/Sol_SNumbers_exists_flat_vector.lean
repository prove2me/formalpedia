-- Prove2me | solution 1 for SNumbers.exists_flat_vector
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:17:44.063619+00:00
-- url     : https://prove2.me/submissions/2ebd9e20-1a5e-4b06-bfc0-d5de72a6776e

module
public import Definitions.Def_SNumbers_Basic
public import Definitions.Def_SNumbers_PiLpCoordinates
public import Mathlib.Analysis.Convex.KreinMilman
public import Definitions.Def_SNumbers_Examples_FlatnessLemmas
public import Theorems.Thm_SNumbers_exists_flat_vector_weighted
public import Theorems.Thm_SNumbers_padFin_apply
attribute [local simp] SNumbers.padFin_apply



set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped ENNReal
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜] {m : ℕ}
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SNumbers
theorem _root_.solution {V : Submodule 𝕜 (Fin m → 𝕜)} {k : ℕ}
    (hk : 1 ≤ k) (hkV : k ≤ Module.finrank 𝕜 V) :
    ∃ x ∈ V, x ≠ 0 ∧ (∀ i, ‖x i‖ ≤ 1) ∧
      k ≤ (Finset.univ.filter (fun i => ‖x i‖ = 1)).card := by
  classical
  obtain ⟨x, hxV, hxle, hxcard⟩ :=
    exists_flat_vector_weighted (V := V) (k := k) (fun _ => (1 : ℝ))
      (fun _ => zero_le_one) hkV
  refine ⟨x, hxV, ?_, hxle, hxcard⟩
  -- At least one coordinate is saturated, so `x` cannot vanish.
  intro hx0
  obtain ⟨i, hi⟩ := Finset.card_pos.mp (le_trans hk hxcard)
  have hxi : ‖x i‖ = 1 := by rw [Finset.mem_filter] at hi; exact hi.2
  rw [hx0] at hxi
  simp at hxi
end SNumbers
