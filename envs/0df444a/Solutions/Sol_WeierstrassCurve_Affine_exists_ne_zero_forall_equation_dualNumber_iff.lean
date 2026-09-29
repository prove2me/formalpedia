-- Prove2me | solution 1 for WeierstrassCurve.Affine.exists_ne_zero_forall_equation_dualNumber_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/5952fa0b-74b0-5e39-9283-18b74282a02d

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_Affine_exists_ne_zero_forall_equation_dualNumber_iff

set_option autoImplicit false

universe u

open TrivSqZeroExt

theorem solution
    {k : Type u} [Field k] (W : WeierstrassCurve.Affine k) (hΔ : W.Δ ≠ 0)
    (x₀ y₀ : k) (h₀ : W.Equation x₀ y₀) :
    ∃ v : k × k, v ≠ 0 ∧
      ∀ x y : DualNumber k, x.fst = x₀ → y.fst = y₀ →
        ((W.map (algebraMap k (DualNumber k))).Equation x y ↔ ∃ c : k, x.snd = c * v.1 ∧ y.snd = c * v.2) := by
  classical
  obtain ⟨-, hgrad⟩ := (W.nonsingular_iff' x₀ y₀).mp ((W.equation_iff_nonsingular_of_Δ_ne_zero hΔ).mp h₀)
  refine ⟨(2 * y₀ + W.a₁ * x₀ + W.a₃, -(W.a₁ * y₀ - (3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄))), ?_, ?_⟩
  · intro h
    obtain ⟨hy, hx⟩ := Prod.mk_eq_zero.mp h
    rcases hgrad with h1 | h1
    · exact h1 (neg_eq_zero.mp hx)
    · exact h1 hy
  · intro x y hx hy
    subst hx hy
    have h₀' := (W.equation_iff' _ _).mp h₀
    have hiff : ∀ z : DualNumber k, z = 0 ↔ z.fst = 0 ∧ z.snd = 0 := fun z =>
      ⟨fun h => by subst h; exact ⟨rfl, rfl⟩, fun h => TrivSqZeroExt.ext h.1 h.2⟩
    have key : (W.map (algebraMap k (DualNumber k))).toAffine.Equation x y ↔
        (W.a₁ * y.fst - (3 * x.fst ^ 2 + 2 * W.a₂ * x.fst + W.a₄)) * x.snd + (2 * y.fst + W.a₁ * x.fst + W.a₃) * y.snd = 0 := by
      rw [WeierstrassCurve.Affine.equation_iff', hiff]
      simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄,
        WeierstrassCurve.map_a₆, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_sub,
        TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_pow, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_sub,
        TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, smul_eq_mul, op_smul_eq_mul,
        pow_succ, pow_zero, one_mul, mul_zero, zero_mul, add_zero, zero_add]
      constructor
      · rintro ⟨-, h2⟩; linear_combination h2
      · intro h2
        refine ⟨by linear_combination h₀', by linear_combination h2⟩
    show (W.map (algebraMap k (DualNumber k))).toAffine.Equation x y ↔ _
    rw [key]
    constructor
    · intro h
      rcases hgrad with hFx | hFy
      · refine ⟨-y.snd / (W.a₁ * y.fst - (3 * x.fst ^ 2 + 2 * W.a₂ * x.fst + W.a₄)), ?_, ?_⟩
        · rw [div_mul_eq_mul_div, eq_div_iff hFx]; linear_combination h
        · rw [div_mul_eq_mul_div, eq_div_iff hFx]; ring
      · refine ⟨x.snd / (2 * y.fst + W.a₁ * x.fst + W.a₃), ?_, ?_⟩
        · exact (div_mul_cancel₀ _ hFy).symm
        · rw [div_mul_eq_mul_div, eq_div_iff hFy]; linear_combination h
    · rintro ⟨c, h1, h2⟩
      rw [h1, h2]; ring

end S_WeierstrassCurve_Affine_exists_ne_zero_forall_equation_dualNumber_iff
end P2MW
export P2MW.S_WeierstrassCurve_Affine_exists_ne_zero_forall_equation_dualNumber_iff (solution)
