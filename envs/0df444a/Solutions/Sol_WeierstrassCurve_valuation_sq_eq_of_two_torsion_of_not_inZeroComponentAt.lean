-- Prove2me | solution 1 for WeierstrassCurve.valuation_sq_eq_of_two_torsion_of_not_inZeroComponentAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/3430bc57-4d1d-5779-9476-1654146bd637

import Mathlib.Algebra.Algebra.Rat
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.LinearCombination
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_valuation_sq_eq_of_two_torsion_of_not_inZeroComponentAt

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem solution
    (W : WeierstrassCurve ℤ) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    {x₀ y₀ : AlgebraicClosure ℚ} (hx₀ : x₀ ∈ A) (hy₀ : y₀ ∈ A)
    (hFy : 2 * y₀ + (W.a₁ : AlgebraicClosure ℚ) * x₀ + W.a₃ = 0)
    (hFx : (W.a₁ : AlgebraicClosure ℚ) * y₀ = 3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄)
    (hnode : A.valuation ((W.b₂ : AlgebraicClosure ℚ) + 12 * x₀) = 1)
    (hbad : A.valuation (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
      - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) < 1)
    {x y : AlgebraicClosure ℚ}
    (h : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular x y)
    (htor : 2 • (Point.some x y h) = 0) (hX : A.valuation (x - x₀) < 1) :
    A.valuation (x - x₀) ^ 2 =
        A.valuation (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀ - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) ∧
      ∀ {x' y' : AlgebraicClosure ℚ}
        (h' : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular x' y'),
        2 • (Point.some x' y' h') = 0 → A.valuation (x' - x₀) < 1 → x' ≠ x →
          A.valuation (x' - x) = A.valuation (x - x₀) := by
  classical

  have _frame : x₀ ∈ A ∧ y₀ ∈ A := ⟨hx₀, hy₀⟩
  have _bad := hbad

  have ha₁ : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).a₁ = (W.a₁ : (AlgebraicClosure ℚ)) := by simp
  have ha₂ : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).a₂ = (W.a₂ : (AlgebraicClosure ℚ)) := by simp
  have ha₃ : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).a₃ = (W.a₃ : (AlgebraicClosure ℚ)) := by simp
  have ha₄ : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).a₄ = (W.a₄ : (AlgebraicClosure ℚ)) := by simp
  have ha₆ : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).a₆ = (W.a₆ : (AlgebraicClosure ℚ)) := by simp
  have hb₂ : (W.b₂ : (AlgebraicClosure ℚ)) = (W.a₁ : (AlgebraicClosure ℚ)) ^ 2 + 4 * (W.a₂ : (AlgebraicClosure ℚ)) := by
    push_cast [WeierstrassCurve.b₂]; ring
  set F₀ : (AlgebraicClosure ℚ) := y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀ - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)
    with hF₀
  set b : (AlgebraicClosure ℚ) := (W.b₂ : (AlgebraicClosure ℚ)) + 12 * x₀ with hb

  have cubic : ∀ {u v : (AlgebraicClosure ℚ)} (huv : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular u v),
      2 • (Point.some u v huv) = 0 → (u - x₀) ^ 2 * (4 * (u - x₀) + b) = 4 * F₀ := by
    intro u v huv htor2
    have heq : v ^ 2 + (W.a₁ : (AlgebraicClosure ℚ)) * u * v + W.a₃ * v
        = u ^ 3 + W.a₂ * u ^ 2 + W.a₄ * u + W.a₆ := by
      have := huv.1
      rw [Affine.equation_iff] at this
      simpa using this
    have h2 : 2 * v + (W.a₁ : (AlgebraicClosure ℚ)) * u + W.a₃ = 0 := by
      rw [two_nsmul, add_eq_zero_iff_eq_neg, Affine.Point.neg_some, Affine.Point.some.injEq] at htor2
      obtain ⟨-, hy⟩ := htor2
      simp only [Affine.negY] at hy
      rw [ha₁, ha₃] at hy
      linear_combination hy
    rw [hb, hb₂, hF₀]
    linear_combination (2 * v + (W.a₁ : (AlgebraicClosure ℚ)) * u + W.a₃) * h2 - 4 * heq
      + (4 * (u - x₀)) * hFx - (2 * (W.a₁ : (AlgebraicClosure ℚ)) * (u - x₀)) * hFy - (2 * y₀ + (W.a₁ : (AlgebraicClosure ℚ)) * x₀ + W.a₃) * hFy

  have hv2 : A.valuation (2 : (AlgebraicClosure ℚ)) = 1 := by
    have hcop : IsCoprime ((2 : ℕ) : ℤ) (q : ℤ) :=
      Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes Nat.prime_two hq).mpr (Ne.symm hq2))
    obtain ⟨a, c, hac⟩ := hcop
    have hacK : (a : (AlgebraicClosure ℚ)) * 2 + (c : (AlgebraicClosure ℚ)) * (q : (AlgebraicClosure ℚ)) = 1 := by
      exact_mod_cast hac
    have h2A : (2 : (AlgebraicClosure ℚ)) ∈ A := by exact_mod_cast natCast_mem A 2
    refine le_antisymm ((A.valuation_le_one_iff _).mpr h2A) (not_lt.mp fun hlt => ?_)
    have hq1 : A.valuation (q : (AlgebraicClosure ℚ)) < 1 := (ValuationSubring.mem_nonunits_iff _).mp hA
    have ha1 : A.valuation (a : (AlgebraicClosure ℚ)) ≤ 1 := (A.valuation_le_one_iff _).mpr (intCast_mem A a)
    have hc1 : A.valuation (c : (AlgebraicClosure ℚ)) ≤ 1 := (A.valuation_le_one_iff _).mpr (intCast_mem A c)
    have hlt1 : A.valuation ((a : (AlgebraicClosure ℚ)) * 2) < 1 := by
      rw [map_mul]
      calc A.valuation (a : (AlgebraicClosure ℚ)) * A.valuation (2 : (AlgebraicClosure ℚ)) ≤ 1 * A.valuation (2 : (AlgebraicClosure ℚ)) :=
            mul_le_mul_of_nonneg_right ha1 zero_le'
        _ < 1 := by rw [one_mul]; exact hlt
    have hlt2 : A.valuation ((c : (AlgebraicClosure ℚ)) * (q : (AlgebraicClosure ℚ))) < 1 := by
      rw [map_mul]
      calc A.valuation (c : (AlgebraicClosure ℚ)) * A.valuation (q : (AlgebraicClosure ℚ)) ≤ 1 * A.valuation (q : (AlgebraicClosure ℚ)) :=
            mul_le_mul_of_nonneg_right hc1 zero_le'
        _ < 1 := by rw [one_mul]; exact hq1
    have := Valuation.map_add_lt A.valuation hlt1 hlt2
    rw [hacK, map_one] at this
    exact lt_irrefl _ this
  have hv4 : A.valuation (4 : (AlgebraicClosure ℚ)) = 1 := by
    rw [show (4 : (AlgebraicClosure ℚ)) = 2 * 2 by norm_num, map_mul, hv2, one_mul]

  have hunit : ∀ {u : (AlgebraicClosure ℚ)}, A.valuation (u - x₀) < 1 → A.valuation (4 * (u - x₀) + b) = 1 := by
    intro u hu
    rw [Valuation.map_add_eq_of_lt_right]
    · exact hnode
    · rw [map_mul, hv4, one_mul, hnode]; exact hu

  have level_sq : ∀ {u v : (AlgebraicClosure ℚ)} (huv : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular u v),
      2 • (Point.some u v huv) = 0 → A.valuation (u - x₀) < 1 →
      A.valuation (u - x₀) ^ 2 = A.valuation F₀ := by
    intro u v huv htor2 hu
    have hc := congrArg A.valuation (cubic huv htor2)
    rw [map_mul, map_pow, hunit hu, mul_one, map_mul, hv4, one_mul] at hc
    exact hc
  refine ⟨level_sq h htor hX, ?_⟩
  intro x' y' h' htor' hX' hne
  have hc := cubic h htor
  have hc' := cubic h' htor'

  have hveq : A.valuation (x' - x₀) = A.valuation (x - x₀) :=
    (pow_left_inj₀ zero_le' zero_le' two_ne_zero).mp ((level_sq h' htor' hX').trans (level_sq h htor hX).symm)

  have hb0 : ∀ ⦃u : (AlgebraicClosure ℚ)⦄, A.valuation (u - x₀) < 1 → 4 * (u - x₀) + b ≠ 0 := by
    intro u hu h0
    have := hunit hu
    rw [h0, _root_.map_zero] at this
    exact zero_ne_one this
  have hX0 : x - x₀ ≠ 0 := by
    intro h0
    have hF : F₀ = 0 := by
      have := hc; rw [h0] at this; simp at this
      exact this
    have : (x' - x₀) ^ 2 * (4 * (x' - x₀) + b) = 0 := by rw [hc', hF, mul_zero]
    rcases mul_eq_zero.mp this with h1 | h1
    · apply hne
      have h1' : x' - x₀ = 0 := (pow_eq_zero_iff two_ne_zero).mp h1
      linear_combination h1' - h0
    · exact hb0 hX' h1
  have hvX0 : A.valuation (x - x₀) ≠ 0 := (Valuation.ne_zero_iff _).mpr hX0

  have hfac : ((x - x₀) - (x' - x₀)) *
      (4 * ((x - x₀) ^ 2 + (x - x₀) * (x' - x₀) + (x' - x₀) ^ 2) + b * ((x - x₀) + (x' - x₀))) = 0 := by
    linear_combination hc - hc'
  have hne' : (x - x₀) - (x' - x₀) ≠ 0 := by
    intro h0; apply hne; linear_combination -h0
  have hsum : b * ((x - x₀) + (x' - x₀))
      = -(4 * ((x - x₀) ^ 2 + (x - x₀) * (x' - x₀) + (x' - x₀) ^ 2)) := by
    have := (mul_eq_zero.mp hfac).resolve_left hne'
    linear_combination this

  have hvsum : A.valuation ((x - x₀) + (x' - x₀)) ≤ A.valuation (x - x₀) ^ 2 := by
    have h1 : A.valuation (b * ((x - x₀) + (x' - x₀))) = A.valuation ((x - x₀) + (x' - x₀)) := by
      rw [map_mul, hnode, one_mul]
    rw [← h1, hsum, Valuation.map_neg, map_mul, hv4, one_mul]
    have e1 : A.valuation ((x - x₀) ^ 2) = A.valuation (x - x₀) ^ 2 := map_pow _ _ _
    have e2 : A.valuation ((x - x₀) * (x' - x₀)) = A.valuation (x - x₀) ^ 2 := by
      rw [map_mul, hveq, sq]
    have e3 : A.valuation ((x' - x₀) ^ 2) = A.valuation (x - x₀) ^ 2 := by rw [map_pow, hveq]
    exact Valuation.map_add_le _ (Valuation.map_add_le _ e1.le e2.le) e3.le

  have hlt : A.valuation ((x - x₀) + (x' - x₀)) < A.valuation (2 * (x - x₀)) := by
    rw [map_mul, hv2, one_mul]
    refine lt_of_le_of_lt hvsum ?_
    calc A.valuation (x - x₀) ^ 2 = A.valuation (x - x₀) * A.valuation (x - x₀) := sq _
      _ < A.valuation (x - x₀) * 1 := mul_lt_mul_of_pos_left hX (zero_lt_iff.mpr hvX0)
      _ = A.valuation (x - x₀) := mul_one _
  have hkey : A.valuation (2 * (x - x₀) - ((x - x₀) + (x' - x₀))) = A.valuation (2 * (x - x₀)) :=
    Valuation.map_sub_eq_of_lt_left _ hlt
  rw [map_mul, hv2, one_mul] at hkey
  have hrw : x' - x = -(2 * (x - x₀) - ((x - x₀) + (x' - x₀))) := by ring
  rw [hrw, Valuation.map_neg, hkey]

end S_WeierstrassCurve_valuation_sq_eq_of_two_torsion_of_not_inZeroComponentAt
end P2MW
export P2MW.S_WeierstrassCurve_valuation_sq_eq_of_two_torsion_of_not_inZeroComponentAt (solution)
