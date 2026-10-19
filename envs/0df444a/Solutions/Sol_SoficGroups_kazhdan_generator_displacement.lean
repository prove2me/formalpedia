-- Prove2me | solution 1 for SoficGroups.kazhdan_generator_displacement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.835808+00:00
-- url     : https://prove2.me/submissions/48b1570b-fcc3-4e6c-ae25-57992aff9989

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
universe u₁ u₂ u₃
namespace SoficGroups
theorem _root_.solution
    {G : Type u} {H : Type v} [Group G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (P : KazhdanPair.{u, v} G)
    (π : UnitaryRepresentation G H)
    (hfixed : ∀ η : H, (∀ g : G, π g η = η) → η = 0)
    (ξ : H) (hξ : ξ ≠ 0) :
    ∃ g ∈ P.generators,
      P.kazhdanConstant * ‖ξ‖ ≤ ‖π g ξ - ξ‖ := by
  classical
  by_contra h
  push Not at h
  have hnorm : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
  let z : ℂ := (‖ξ‖ : ℂ)⁻¹
  let ζ : H := z • ξ
  have hζ : ‖ζ‖ = 1 := by
    dsimp [ζ, z]
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hnorm]
    exact inv_mul_cancel₀ (ne_of_gt hnorm)
  have hζsmall : ∀ g ∈ P.generators,
      ‖π g ζ - ζ‖ < P.kazhdanConstant := by
    intro g hg
    have hscale :
        ‖π g ζ - ζ‖ = ‖ξ‖⁻¹ * ‖π g ξ - ξ‖ := by
      dsimp [ζ, z]
      rw [map_smul, ← smul_sub, norm_smul, norm_inv, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hnorm]
    rw [hscale]
    calc
      ‖ξ‖⁻¹ * ‖π g ξ - ξ‖ <
          ‖ξ‖⁻¹ * (P.kazhdanConstant * ‖ξ‖) :=
        mul_lt_mul_of_pos_left (h g hg) (inv_pos.mpr hnorm)
      _ = P.kazhdanConstant := by
        field_simp
  obtain ⟨η, hη, hηfixed⟩ := P.invariant H π ζ hζ hζsmall
  exact hη (hfixed η hηfixed)
end SoficGroups
