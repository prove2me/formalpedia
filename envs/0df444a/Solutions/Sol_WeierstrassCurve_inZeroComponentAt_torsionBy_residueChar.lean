-- Prove2me | solution 1 for WeierstrassCurve.inZeroComponentAt_torsionBy_residueChar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/8946c20f-192f-5944-9e49-982c97bd30b5

import Theorems.Thm_WeierstrassCurve_Affine_Point_eq_zero_of_prime_smul_eq_zero_of_isNode
import Theorems.Thm_WeierstrassCurve_exists_reduction_inZeroComponentAt
import Theorems.Thm_WeierstrassCurve_inZeroComponentAt_sub
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_ZeroComponentAt
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.Lie.OfAssociative
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_inZeroComponentAt_torsionBy_residueChar

p2m_open "WeierstrassCurve P2MW.S_WeierstrassCurve_inZeroComponentAt_torsionBy_residueChar.WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point"

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine map_c₄ Affine.equation_iff' a₃ c_relation a₁ map b₂ a₄ a₂ a₆ Affine.nonsingular_iff' c₆ reduction toAffine Affine.Point map_Δ b₆ Δ c₄ b₄ exists_reduction_inZeroComponentAt InZeroComponentAt inZeroComponentAt_sub"
p2m_open "WeierstrassCurve"

variable {k : Type*} [Field k] (V : WeierstrassCurve k)

private lemma _root_.WeierstrassCurve.four_mul_poly (x y : k) :
    4 * (y ^ 2 + V.a₁ * x * y + V.a₃ * y - (x ^ 3 + V.a₂ * x ^ 2 + V.a₄ * x + V.a₆)) =
      (2 * y + V.a₁ * x + V.a₃) ^ 2 - (4 * x ^ 3 + V.b₂ * x ^ 2 + 2 * V.b₄ * x + V.b₆) := by
  simp only [b₂, b₄, b₆]; ring

p2m_export "WeierstrassCurve" "four_mul_poly"

private lemma _root_.WeierstrassCurve.deriv_twoTorsion (x y : k) :
    12 * x ^ 2 + 2 * V.b₂ * x + 2 * V.b₄ =
      2 * V.a₁ * (2 * y + V.a₁ * x + V.a₃) - 4 * (V.a₁ * y - (3 * x ^ 2 + 2 * V.a₂ * x + V.a₄)) := by
  simp only [b₂, b₄]; ring

p2m_export "WeierstrassCurve" "deriv_twoTorsion"
private theorem _root_.WeierstrassCurve.exists_isNode_of_Δ_eq_zero (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (hΔ : V.Δ = 0)
    (hc₄ : V.c₄ ≠ 0) :
    ∃ x₀ y₀ : k, V.toAffine.Equation x₀ y₀ ∧ ¬ V.toAffine.Nonsingular x₀ y₀ ∧
      V.b₂ + 12 * x₀ ≠ 0 := by
  have h12 : (12 : k) ≠ 0 := by
    have : (12 : k) = 2 * 2 * 3 := by norm_num
    rw [this]; exact mul_ne_zero (mul_ne_zero h2 h2) h3
  have hD : 12 * V.c₄ ≠ 0 := mul_ne_zero h12 hc₄
  set x₀ : k := -(V.b₂ * V.c₄ + V.c₆) / (12 * V.c₄) with hx₀
  set y₀ : k := -(V.a₁ * x₀ + V.a₃) / 2 with hy₀
  have hrel : V.c₄ ^ 3 - V.c₆ ^ 2 = 0 := by rw [← c_relation, hΔ, mul_zero]

  have hf : 4 * x₀ ^ 3 + V.b₂ * x₀ ^ 2 + 2 * V.b₄ * x₀ + V.b₆ = 0 := by
    have key : (12 * V.c₄) ^ 3 * (4 * x₀ ^ 3 + V.b₂ * x₀ ^ 2 + 2 * V.b₄ * x₀ + V.b₆) =
        4 * V.c₆ * (V.c₄ ^ 3 - V.c₆ ^ 2) := by
      rw [hx₀]; field_simp; simp only [c₄, c₆]; ring
    rw [hrel, mul_zero] at key
    exact (mul_eq_zero.mp key).resolve_left (pow_ne_zero _ hD)
  have hf' : 12 * x₀ ^ 2 + 2 * V.b₂ * x₀ + 2 * V.b₄ = 0 := by
    have key : (12 * V.c₄) ^ 2 * (12 * x₀ ^ 2 + 2 * V.b₂ * x₀ + 2 * V.b₄) =
        12 * (V.c₆ ^ 2 - V.c₄ ^ 3) := by
      rw [hx₀]; field_simp; simp only [c₄, c₆]; ring
    rw [show V.c₆ ^ 2 - V.c₄ ^ 3 = -(V.c₄ ^ 3 - V.c₆ ^ 2) by ring, hrel, _root_.neg_zero, mul_zero] at key
    exact (mul_eq_zero.mp key).resolve_left (pow_ne_zero _ hD)
  have hFy : 2 * y₀ + V.a₁ * x₀ + V.a₃ = 0 := by
    rw [hy₀]; field_simp; ring
  have hFx : V.a₁ * y₀ - (3 * x₀ ^ 2 + 2 * V.a₂ * x₀ + V.a₄) = 0 := by
    have hder := V.deriv_twoTorsion x₀ y₀
    rw [hf', hFy, mul_zero, zero_sub] at hder
    have h4 : (4 : k) ≠ 0 := by
      have : (4 : k) = 2 * 2 := by norm_num
      rw [this]; exact mul_ne_zero h2 h2

    have h' : 4 * (V.a₁ * y₀ - (3 * x₀ ^ 2 + 2 * V.a₂ * x₀ + V.a₄)) = 0 :=
      neg_eq_zero.mp hder.symm
    exact (mul_eq_zero.mp h').resolve_left h4
  have heq : V.toAffine.Equation x₀ y₀ := by
    rw [Affine.equation_iff']
    have h4 : (4 : k) ≠ 0 := by
      have : (4 : k) = 2 * 2 := by norm_num
      rw [this]; exact mul_ne_zero h2 h2
    have := V.four_mul_poly x₀ y₀
    rw [hFy, hf, zero_pow two_ne_zero, sub_zero] at this
    exact (mul_eq_zero.mp this).resolve_left h4
  refine ⟨x₀, y₀, heq, ?_, ?_⟩
  · rw [Affine.nonsingular_iff']
    push Not
    exact fun _ => ⟨hFx, hFy⟩
  ·
    intro h0
    apply hc₄
    have : (V.b₂ + 12 * x₀) ^ 2 - V.c₄ = 12 * (12 * x₀ ^ 2 + 2 * V.b₂ * x₀ + 2 * V.b₄) := by
      simp only [c₄]; ring
    rw [h0, hf', mul_zero, zero_pow two_ne_zero, zero_sub, neg_eq_zero] at this
    exact this

p2m_export "WeierstrassCurve" "exists_isNode_of_Δ_eq_zero"
end WeierstrassCurve

section TFE1
open IsLocalRing

lemma charP_residueField_of_liesOverPrime' (A : ValuationSubring (AlgebraicClosure ℚ)) {q : ℕ}
    (hq : q.Prime) (hA : A.LiesOverPrime q) : CharP (ResidueField A) q := by
  rw [CharP.charP_iff_prime_eq_zero hq]
  have hmem : ((q : A) : AlgebraicClosure ℚ) ∈ A.nonunits := by simp at hA ⊢; exact hA
  have hmax : (q : A) ∈ IsLocalRing.maximalIdeal A := (A.coe_mem_nonunits_iff).mp hmem
  simpa using (IsLocalRing.residue_eq_zero_iff (q : A)).mpr hmax

lemma inZeroComponentAt_nsmul (W : WeierstrassCurve ℤ) (A : ValuationSubring (AlgebraicClosure ℚ))
    {P : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point} (hP : W.InZeroComponentAt A P)
    (n : ℕ) : W.InZeroComponentAt A (n • P) := by
  have h0 : W.InZeroComponentAt A 0 := Or.inl rfl
  induction n with
  | zero => (simp at h0 ⊢; exact h0)
  | succ n ih =>
    rw [succ_nsmul, ← sub_neg_eq_add]
    exact W.inZeroComponentAt_sub A ih (by exact W.inZeroComponentAt_sub A h0 hP)

theorem solution
    (W : WeierstrassCurve ℤ) {q : ℕ} (hq : q.Prime) (hq5 : 5 ≤ q) (hΔ : W.Δ ≠ 0)
    (hqΔ : (q : ℤ) ∣ W.Δ) (hqc₄ : ¬ (q : ℤ) ∣ W.c₄)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (t : Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point q)
    (ht : W.InZeroComponentAt A (t : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point)) :
    (t : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) = 0 ∨
      ∃ (x y : AlgebraicClosure ℚ) (h : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular x y),
        (t : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) = .some x y h ∧ x ∉ A := by
  classical
  have := hΔ
  rcases ht with h0 | ⟨x, y, h, hP, hx | ⟨hx, hy, hns⟩⟩
  · exact Or.inl h0
  · exact Or.inr ⟨x, y, h, hP, hx⟩
  ·
    exfalso
    set k := ResidueField A
    haveI : Fact q.Prime := ⟨hq⟩
    haveI hchar : CharP k q := charP_residueField_of_liesOverPrime' A hq hA
    have h2 : (2 : k) ≠ 0 := by
      rw [show (2 : k) = ((2 : ℕ) : k) by norm_num, Ne, CharP.cast_eq_zero_iff k q]
      intro hd; have := Nat.le_of_dvd (by norm_num) hd; omega
    have h3 : (3 : k) ≠ 0 := by
      rw [show (3 : k) = ((3 : ℕ) : k) by norm_num, Ne, CharP.cast_eq_zero_iff k q]
      intro hd; have := Nat.le_of_dvd (by norm_num) hd; omega

    set Wk : WeierstrassCurve k := W.map (Int.castRingHom k) with hWk
    have hΔk : Wk.Δ = 0 := by
      rw [hWk, map_Δ]
      obtain ⟨m, hm⟩ := hqΔ
      rw [hm, map_mul, map_natCast, CharP.cast_eq_zero, zero_mul]
    have hc₄k : Wk.c₄ ≠ 0 := by
      rw [hWk, map_c₄]
      intro h0
      exact hqc₄ ((CharP.intCast_eq_zero_iff k q W.c₄).mp (by simpa using h0))
    obtain ⟨x₀, y₀, he, hs, hnode⟩ := Wk.exists_isNode_of_Δ_eq_zero h2 h3 hΔk hc₄k

    obtain ⟨red, hred0, hadd, hsome, -, -, -⟩ := W.exists_reduction_inZeroComponentAt A
    set P : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point := Point.some x y h with hPdef
    have hPin : W.InZeroComponentAt A P := Or.inr ⟨x, y, h, rfl, Or.inr ⟨hx, hy, hns⟩⟩

    have hmul : ∀ n : ℕ, red (n • P) = n • red P := by
      intro n
      induction n with
      | zero => simp [hred0]
      | succ n ih =>
        rw [succ_nsmul, hadd _ _ (inZeroComponentAt_nsmul W A hPin n) hPin, ih, succ_nsmul]

    have hqP : q • P = 0 := by
      have := t.property
      rw [Submodule.mem_torsionBy_iff] at this
      have h' : (q : ℤ) • ((t : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point)) = 0 := this
      rwa [hP, natCast_zsmul] at h'
    have hqred : q • red P = 0 := by rw [← hmul, hqP, hred0]

    have hzero := Point.eq_zero_of_prime_smul_eq_zero_of_isNode Wk x₀ y₀ he hs hnode (red P) hqred
    rw [hPdef, hsome x y h hx hy hns] at hzero
    exact Point.some_ne_zero _ hzero

end TFE1

end S_WeierstrassCurve_inZeroComponentAt_torsionBy_residueChar
end P2MW
export P2MW.S_WeierstrassCurve_inZeroComponentAt_torsionBy_residueChar (solution)
