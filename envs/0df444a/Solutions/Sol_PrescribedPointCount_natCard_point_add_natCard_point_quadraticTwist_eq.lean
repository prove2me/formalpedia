-- Prove2me | solution 1 for PrescribedPointCount.natCard_point_add_natCard_point_quadraticTwist_eq
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-18T21:28:10.14662+00:00
-- url     : https://prove2.me/submissions/9b716035-f539-4402-8bee-f0987745a454

import Mathlib

namespace TwAux

open WeierstrassCurve

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

noncomputable def ptEquiv (W : WeierstrassCurve.Affine F) :
    W.Point ≃ Option {xy : F × F // W.Nonsingular xy.1 xy.2} where
  toFun
    | .zero => none
    | .some x y h => some ⟨(x, y), h⟩
  invFun
    | none => .zero
    | some ⟨(x, y), h⟩ => .some x y h
  left_inv P := by cases P <;> rfl
  right_inv o := by
    rcases o with _ | ⟨⟨x, y⟩, h⟩ <;> rfl

lemma card_fiber (hF : ringChar F ≠ 2) (c : F) :
    (Nat.card {y : F // y ^ 2 = c} : ℤ) = quadraticChar F c + 1 := by
  rw [← quadraticChar_card_sqrts hF c]
  rw [← Nat.card_eq_card_toFinset]
  rfl

lemma card_points (A B : F) (hΔ : (WeierstrassCurve.mk 0 0 0 A B).Δ ≠ 0)
    (hF : ringChar F ≠ 2) :
    (Nat.card (WeierstrassCurve.mk 0 0 0 A B).toAffine.Point : ℤ) =
      ∑ x : F, (quadraticChar F (x ^ 3 + A * x + B) + 1) + 1 := by
  classical
  set W := (WeierstrassCurve.mk 0 0 0 A B).toAffine
  have e1 := Nat.card_congr (ptEquiv W)
  rw [e1, Finite.card_option]
  have e2 : {xy : F × F // W.Nonsingular xy.1 xy.2} ≃
      {xy : F × F // xy.2 ^ 2 = xy.1 ^ 3 + A * xy.1 + B} := by
    apply Equiv.subtypeEquivRight
    intro xy
    rw [← Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔ, Affine.equation_iff]
    simp
  rw [Nat.card_congr e2,
    Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype
      (fun (x y : F) => y ^ 2 = x ^ 3 + A * x + B))]
  rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
  push_cast
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  rw [← card_fiber hF, Nat.card_eq_fintype_card]

end TwAux

open TwAux in
theorem solution (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (a b d : ZMod p) (hd : ¬ IsSquare d)
    (hE : (WeierstrassCurve.mk 0 0 0 a b).IsElliptic) :
    Nat.card (WeierstrassCurve.mk 0 0 0 a b).toAffine.Point +
        Nat.card (WeierstrassCurve.mk 0 0 0 (d ^ 2 * a) (d ^ 3 * b)).toAffine.Point =
      2 * (p + 1) := by
  have hF : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp
  have hd0 : d ≠ 0 := by rintro rfl; exact hd ⟨0, by simp⟩
  have hΔ : (WeierstrassCurve.mk 0 0 0 a b).Δ ≠ 0 := hE.isUnit.ne_zero
  have hΔ' : (WeierstrassCurve.mk 0 0 0 (d ^ 2 * a) (d ^ 3 * b)).Δ ≠ 0 := by
    have : (WeierstrassCurve.mk 0 0 0 (d ^ 2 * a) (d ^ 3 * b)).Δ =
        d ^ 6 * (WeierstrassCurve.mk 0 0 0 a b).Δ := by
      simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
        WeierstrassCurve.b₆, WeierstrassCurve.b₈]
      ring
    rw [this]; exact mul_ne_zero (pow_ne_zero _ hd0) hΔ
  have hχd : quadraticChar (ZMod p) d = -1 := quadraticChar_neg_one_iff_not_isSquare.mpr hd
  have h1 := card_points a b hΔ hF
  have h2 := card_points (d ^ 2 * a) (d ^ 3 * b) hΔ' hF
  have hre : ∑ x : ZMod p, (quadraticChar (ZMod p) (x ^ 3 + d ^ 2 * a * x + d ^ 3 * b) + 1) =
      ∑ x : ZMod p, (-quadraticChar (ZMod p) (x ^ 3 + a * x + b) + 1) := by
    refine (Fintype.sum_equiv (Equiv.mulLeft₀ d hd0) _ _ (fun x => ?_)).symm
    show _ = quadraticChar (ZMod p) ((d * x) ^ 3 + d ^ 2 * a * (d * x) + d ^ 3 * b) + 1
    have : (d * x) ^ 3 + d ^ 2 * a * (d * x) + d ^ 3 * b = d ^ 3 * (x ^ 3 + a * x + b) := by ring
    rw [this, map_mul, map_pow, hχd]
    ring
  rw [hre] at h2
  have : ((Nat.card (WeierstrassCurve.mk 0 0 0 a b).toAffine.Point +
      Nat.card (WeierstrassCurve.mk 0 0 0 (d ^ 2 * a) (d ^ 3 * b)).toAffine.Point : ℕ) : ℤ) =
      ((2 * (p + 1) : ℕ) : ℤ) := by
    push_cast
    rw [h1, h2, add_add_add_comm, ← Finset.sum_add_distrib]
    have : ∀ x : ZMod p, (quadraticChar (ZMod p) (x ^ 3 + a * x + b) + 1) +
        (-quadraticChar (ZMod p) (x ^ 3 + a * x + b) + 1) = 2 := fun x => by ring
    simp only [this, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
    push_cast; ring
  exact_mod_cast this
