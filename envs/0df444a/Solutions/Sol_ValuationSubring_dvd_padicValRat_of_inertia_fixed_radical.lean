-- Prove2me | solution 1 for ValuationSubring.dvd_padicValRat_of_inertia_fixed_radical
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:02:31.42066+00:00
-- url     : https://prove2.me/submissions/78fc4227-7958-4a1c-9496-8e741dcae50b

import Theorems.Thm_ValuationSubring_isDiscreteValuationRing_comap_fixedField_inertiaSubgroupIn
import Theorems.Thm_ValuationSubring_valuation_ratCast_eq_zpow_padicValRat

set_option autoImplicit false

namespace ValuationSubring

/-- An inertia-fixed radical of a rational unit has integral normalized
valuation, so its exponent divides the rational prime valuation. -/
theorem _root_.solution
    (A : ValuationSubring (AlgebraicClosure ℚ)) (q : ℕ) [Fact q.Prime]
    (hA : A.LiesOverPrime q) (m : ℕ) (a : ℚˣ) (α : (AlgebraicClosure ℚ)ˣ)
    (hα : (α : AlgebraicClosure ℚ) ^ m = (a : ℚ))
    (hfix : ∀ σ ∈ A.inertiaSubgroupIn ℚ, σ (α : AlgebraicClosure ℚ) = α) :
    (m : ℤ) ∣ padicValRat q (a : ℚ) := by
  let F := IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)
  let B := A.comap (algebraMap F (AlgebraicClosure ℚ))
  obtain ⟨hdvr, hqirr, _, _⟩ :=
    isDiscreteValuationRing_comap_fixedField_inertiaSubgroupIn A q hA
  letI : IsDiscreteValuationRing B := hdvr
  have hαF : (α : AlgebraicClosure ℚ) ∈ F := by
    rw [IntermediateField.mem_fixedField_iff]
    exact hfix
  let y : F := ⟨α, hαF⟩
  have hy0 : y ≠ 0 := by
    intro h
    exact α.ne_zero (congrArg Subtype.val h)
  obtain ⟨n, u, hy⟩ :=
    IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible
      (R := B) (K := F) (ϖ := (q : B)) hqirr hy0
  let j : B →+* A :=
    { toFun := fun b => ⟨algebraMap F (AlgebraicClosure ℚ) b, b.property⟩
      map_zero' := Subtype.ext (map_zero _)
      map_one' := Subtype.ext (map_one _)
      map_add' := fun b c => Subtype.ext
        (map_add (algebraMap F (AlgebraicClosure ℚ)) (b : F) (c : F))
      map_mul' := fun b c => Subtype.ext
        (map_mul (algebraMap F (AlgebraicClosure ℚ)) (b : F) (c : F)) }
  have hu : A.valuation (algebraMap F (AlgebraicClosure ℚ) (u : B)) = 1 :=
    A.valuation_unit (Units.map j.toMonoidHom u)
  have heq : (α : AlgebraicClosure ℚ) =
      algebraMap F (AlgebraicClosure ℚ) (u : B) * (q : AlgebraicClosure ℚ) ^ n := by
    change y = algebraMap B F (u : B) * (algebraMap B F (q : B)) ^ n at hy
    rw [map_natCast] at hy
    have h := congrArg (algebraMap F (AlgebraicClosure ℚ)) hy
    change (α : AlgebraicClosure ℚ) =
      algebraMap F (AlgebraicClosure ℚ) (algebraMap B F (u : B) * (q : F) ^ n) at h
    rw [map_mul, map_zpow₀, map_natCast] at h
    exact h
  have hval : A.valuation (α : AlgebraicClosure ℚ) =
      A.valuation (q : AlgebraicClosure ℚ) ^ n := by
    rw [heq, map_mul, map_zpow₀, hu, one_mul]
  have hqval : A.valuation (q : AlgebraicClosure ℚ) < 1 := hA
  have hq0 : A.valuation (q : AlgebraicClosure ℚ) ≠ 0 := by
    exact (map_ne_zero _).mpr (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero)
  have hp := congrArg A.valuation hα
  rw [map_pow, hval,
    A.valuation_ratCast_eq_zpow_padicValRat (Fact.out : q.Prime) hqval a.ne_zero,
    ← zpow_natCast, ← zpow_mul] at hp
  have hexp : n * (m : ℤ) = padicValRat q (a : ℚ) :=
    (zpow_right_strictAnti₀ (pos_iff_ne_zero.mpr hq0) hqval).injective hp
  exact ⟨n, by rw [← hexp, mul_comm]⟩

end ValuationSubring
