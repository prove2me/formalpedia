-- Prove2me | solution 1 for WeierstrassCurve.reduceHom_surjective_of_henselianLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/9c8f2203-b610-5cb2-b1cd-73e623dd9f2e

import Mathlib
import Definitions.Def_WeierstrassCurve_ReduceHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_reduceHom_surjective_of_henselianLocalRing

set_option autoImplicit false

p2m_open "WeierstrassCurve P2MW.S_WeierstrassCurve_reduceHom_surjective_of_henselianLocalRing.WeierstrassCurve IsLocalRing Polynomial"

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine Affine.equation_iff' a₃ a₁ WeierstrassCurve.map_a₃ map isElliptic_iff a₄ a₂ a₆ Affine.nonsingular_iff' WeierstrassCurve.map_a₆ reduction toAffine WeierstrassCurve.map_a₂ WeierstrassCurve.map_a₁ WeierstrassCurve.map_a₄ map_Δ map_a₆ map_a₁ Affine.equation_iff_nonsingular map_a₄ Δ map_a₂ map_a₃ reduceHom Affine.Y_mem_of_X_mem map_residue_Δ_ne_zero_iff reducePoint reducePoint_some_of_mem"
namespace ReduceSurjective
p2m_open "WeierstrassCurve"

variable {L : Type*} [Field L] [DecidableEq L] {A : ValuationSubring L} [HenselianLocalRing A]
variable [DecidableEq (ResidueField A)]
variable {W : WeierstrassCurve A} (hΔ : (W.map (residue A)).Δ ≠ 0)

include hΔ in
theorem isElliptic_map_subtype : (W.map A.subtype).IsElliptic := by
  have hu : IsUnit W.Δ := (map_residue_Δ_ne_zero_iff W).mp hΔ
  rw [isElliptic_iff, map_Δ]
  exact hu.map A.subtype

noncomputable def polyY (W : WeierstrassCurve A) (x₀ : A) : A[X] :=
  X ^ 2 + (C (W.a₁ * x₀ + W.a₃) * X - C (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆))

noncomputable def polyX (W : WeierstrassCurve A) (y₀ : A) : A[X] :=
  X ^ 3 + (C W.a₂ * X ^ 2 + C (W.a₄ - W.a₁ * y₀) * X + C (W.a₆ - y₀ ^ 2 - W.a₃ * y₀))

omit [DecidableEq L] [HenselianLocalRing A] in
theorem monic_polyY (x₀ : A) : (polyY W x₀).Monic := by
  refine (monic_X_pow 2).add_of_left ?_
  calc degree (C (W.a₁ * x₀ + W.a₃) * X - C (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆))
      ≤ 1 := (degree_sub_le _ _).trans (max_le (degree_C_mul_X_le _) (degree_C_le.trans (by norm_num)))
    _ < degree ((X : A[X]) ^ 2) := by rw [degree_X_pow]; norm_num

omit [DecidableEq L] [HenselianLocalRing A] in
theorem monic_polyX (y₀ : A) : (polyX W y₀).Monic := by
  refine (monic_X_pow 3).add_of_left ?_
  calc degree (C W.a₂ * X ^ 2 + C (W.a₄ - W.a₁ * y₀) * X + C (W.a₆ - y₀ ^ 2 - W.a₃ * y₀))
      ≤ 2 := by
        refine (degree_add_le _ _).trans (max_le ((degree_add_le _ _).trans (max_le ?_ ?_)) ?_)
        · exact (degree_C_mul_X_pow_le 2 _)
        · exact (degree_C_mul_X_le _).trans (by norm_num)
        · exact degree_C_le.trans (by norm_num)
    _ < degree ((X : A[X]) ^ 3) := by rw [degree_X_pow]; norm_num

omit [DecidableEq L] [HenselianLocalRing A] [DecidableEq (ResidueField A)] in

theorem map_residue_a (W : WeierstrassCurve A) :
    (W.map (residue A)).a₁ = residue A W.a₁ ∧ (W.map (residue A)).a₂ = residue A W.a₂ ∧
      (W.map (residue A)).a₃ = residue A W.a₃ ∧ (W.map (residue A)).a₄ = residue A W.a₄ ∧
        (W.map (residue A)).a₆ = residue A W.a₆ :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

include hΔ in

theorem reduceHom_surjective : Function.Surjective (WeierstrassCurve.reduceHom hΔ) := by
  haveI := isElliptic_map_subtype hΔ
  rintro (_ | ⟨xb, yb, hb⟩)
  · exact ⟨0, map_zero _⟩
  · obtain ⟨x₀, rfl⟩ := IsLocalRing.residue_surjective xb
    obtain ⟨y₀, rfl⟩ := IsLocalRing.residue_surjective yb
    obtain ⟨heq, hpartial⟩ := (Affine.nonsingular_iff' _ _).mp hb
    rw [Affine.equation_iff'] at heq
    obtain ⟨ha₁, ha₂, ha₃, ha₄, ha₆⟩ := map_residue_a W
    simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at heq hpartial

    have mkPt : ∀ (x y : A), (polyY W x).eval y = 0 → residue A x = residue A x₀ →
        residue A y = residue A y₀ →
        ∃ P : (W.map A.subtype).toAffine.Point,
          WeierstrassCurve.reduceHom hΔ P = .some (residue A x₀) (residue A y₀) hb := by
      intro x y hxy hx hy
      have heqA : W.toAffine.Equation x y := by
        rw [Affine.equation_iff']
        simp only [polyY, eval_add, eval_mul, eval_pow, eval_C, eval_X, eval_sub] at hxy
        change y ^ 2 + W.a₁ * x * y + W.a₃ * y - (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) = 0
        linear_combination hxy
      have heqL : (W.map A.subtype).toAffine.Equation (x : L) (y : L) :=
        (W.toAffine.map_equation A.subtype_injective x y).mpr heqA
      have hnsL : (W.map A.subtype).toAffine.Nonsingular (x : L) (y : L) :=
        Affine.equation_iff_nonsingular.mp heqL
      refine ⟨.some _ _ hnsL, ?_⟩
      change reducePoint hΔ (.some (x : L) (y : L) hnsL) = _
      rw [reducePoint_some_of_mem hΔ hnsL (SetLike.coe_mem x)]
      have hx' : residue A ⟨(x : L), SetLike.coe_mem x⟩ = residue A x₀ := by
        rw [← hx]
      have hy' : residue A ⟨(y : L), Affine.Y_mem_of_X_mem W hnsL.1 (SetLike.coe_mem x)⟩ =
          residue A y₀ := by
        rw [← hy]
      simp only [hx', hy']
    rcases hpartial with hX | hY
    ·
      have h1 : (polyX W y₀).eval x₀ ∈ maximalIdeal A := by
        rw [← residue_eq_zero_iff]
        simp only [polyX, eval_add, eval_mul, eval_pow, eval_C, eval_X, eval_sub, map_add,
          map_mul, map_pow, map_sub]
        linear_combination (-1 : ResidueField A) * heq
      have h2 : IsUnit ((polyX W y₀).derivative.eval x₀) := by
        rw [← residue_ne_zero_iff_isUnit]
        have hder : (polyX W y₀).derivative.eval x₀ =
            3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + (W.a₄ - W.a₁ * y₀) := by
          simp only [polyX, derivative_add, derivative_mul, derivative_X_pow, derivative_C,
            derivative_X, eval_add, eval_mul, eval_pow, eval_C, eval_X, eval_ofNat, eval_zero, eval_one]
          ring
        rw [hder]
        intro h0
        apply hX
        simp only [map_add, map_mul, map_pow, map_sub, map_ofNat] at h0
        linear_combination (-1 : ResidueField A) * h0
      obtain ⟨x, hroot, hx⟩ := HenselianLocalRing.is_henselian (polyX W y₀) (monic_polyX y₀) x₀ h1 h2
      refine mkPt x y₀ ?_ ?_ rfl
      · have : (polyX W y₀).eval x = 0 := hroot
        simp only [polyX, eval_add, eval_mul, eval_pow, eval_C, eval_X, eval_sub] at this
        simp only [polyY, eval_add, eval_mul, eval_pow, eval_C, eval_X, eval_sub]
        linear_combination (-1 : A) * this
      · rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
        exact hx
    ·
      have h1 : (polyY W x₀).eval y₀ ∈ maximalIdeal A := by
        rw [← residue_eq_zero_iff]
        simp only [polyY, eval_add, eval_mul, eval_pow, eval_C, eval_X, eval_sub, map_add,
          map_mul, map_pow, map_sub]
        linear_combination heq
      have h2 : IsUnit ((polyY W x₀).derivative.eval y₀) := by
        rw [← residue_ne_zero_iff_isUnit]
        have hder : (polyY W x₀).derivative.eval y₀ = 2 * y₀ + (W.a₁ * x₀ + W.a₃) := by
          simp only [polyY, derivative_add, derivative_sub, derivative_mul, derivative_X_pow,
            derivative_C, derivative_X, eval_add, eval_sub, eval_mul, eval_pow, eval_C, eval_X,
            eval_ofNat, eval_zero, eval_one]
          ring
        rw [hder]
        intro h0
        apply hY
        simp only [map_add, map_mul, map_ofNat] at h0
        linear_combination h0
      obtain ⟨y, hroot, hy⟩ := HenselianLocalRing.is_henselian (polyY W x₀) (monic_polyY x₀) y₀ h1 h2
      refine mkPt x₀ y hroot rfl ?_
      rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
      exact hy

end WeierstrassCurve.ReduceSurjective

theorem solution
    {L : Type*} [Field L] [DecidableEq L] {A : ValuationSubring L} [HenselianLocalRing A]
    [DecidableEq (IsLocalRing.ResidueField A)]
    {W : WeierstrassCurve A} (hΔ : (W.map (IsLocalRing.residue A)).Δ ≠ 0) :
    Function.Surjective (WeierstrassCurve.reduceHom hΔ) :=
  WeierstrassCurve.ReduceSurjective.reduceHom_surjective hΔ

end S_WeierstrassCurve_reduceHom_surjective_of_henselianLocalRing
end P2MW
export P2MW.S_WeierstrassCurve_reduceHom_surjective_of_henselianLocalRing (solution)
