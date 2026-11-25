-- Prove2me | solution 1 for SteerableE2CNN.pointwise_nonlinearity_quotient_equivariant
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T10:37:59.641804+00:00
-- url     : https://prove2.me/submissions/b7f9d57c-76b8-46bf-8b8d-24acb3d95d50

import Mathlib
import Definitions.Def_SteerableE2CNN_Basic

set_option autoImplicit false

open Matrix MeasureTheory
namespace SteerableE2CNN

open Classical in
lemma pq_apply {G : Type*} [Group G] [Fintype G]
    (H : Subgroup G) (g : G) (v : G ⧸ H → ℝ) (a : G ⧸ H) :
    (quotRep H g *ᵥ v) a = v (g⁻¹ • a) := by
  simp only [Matrix.mulVec, dotProduct, quotRep, Matrix.of_apply]
  have : ∀ b : G ⧸ H, (if a = g • b then (1:ℝ) else 0) * v b
      = if g⁻¹ • a = b then v b else 0 := by
    intro b
    have e : (a = g • b) ↔ (g⁻¹ • a = b) := by
      constructor
      · rintro rfl; simp
      · rintro rfl; simp
    by_cases h : a = g • b
    · rw [if_pos h, if_pos (e.1 h)]; ring
    · rw [if_neg h, if_neg (fun h' => h (e.2 h'))]; ring
  rw [Finset.sum_congr rfl (fun b _ => this b)]
  simp

open Classical in
theorem pointwise_nonlinearity_quotient_equivariant {G : Type*} [Group G] [Fintype G]
    (H : Subgroup G) (σ : ℝ → ℝ) (g : G) (v : G ⧸ H → ℝ) :
    (fun a => σ ((quotRep H g *ᵥ v) a)) = quotRep H g *ᵥ (fun a => σ (v a)) := by
  funext a
  rw [pq_apply, pq_apply]

end SteerableE2CNN

open SteerableE2CNN in
open Classical in
theorem solution {G : Type*} [Group G] [Fintype G]
    (H : Subgroup G) (σ : ℝ → ℝ) (g : G) (v : G ⧸ H → ℝ) :
    (fun a => σ ((quotRep H g *ᵥ v) a)) = quotRep H g *ᵥ (fun a => σ (v a)) :=
  SteerableE2CNN.pointwise_nonlinearity_quotient_equivariant H σ g v
