-- Prove2me | solution 1 for PrescribedPointCount.exists_isElliptic_trace_eq_of_dvd
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-24T22:26:47.564808+00:00
-- url     : https://prove2.me/submissions/5b7c877d-3f41-43aa-86e7-8fc42eefecd6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_LefebvreVariations_exists_supersingular_of_mod_twelve_eq_one
set_option autoImplicit false

/-! Reduction of `PrescribedPointCount.exists_isElliptic_trace_eq_of_dvd` (the supersingular case
of Deuring's theorem over prime fields) to the variation
`LefebvreVariations.exists_supersingular_of_mod_twelve_eq_one`: every prime `p ≡ 1 (mod 12)`
carries an elliptic curve with exactly `p + 1` points. The variation is the only open step.

Everything else is proved here:
* `#E(𝔽_q) = 1 + #{(x, y) : W(x, y) = 0}` for an elliptic curve, and for `y² = x³ + ax + b` in odd
  characteristic `#E = q + 1 + Σₓ χ(x³ + ax + b)` (`χ` the quadratic character);
* `y² = x³ − x` has `p + 1` points when `p ≡ 3 (mod 4)` (the character sum is odd under `x ↦ −x`);
* `y² = x³ + 1` has `p + 1` points when `p ≡ 2 (mod 3)` (`x ↦ x³` is a bijection);
* over `𝔽₂` and `𝔽₃` the traces `±p` (and `0` over `𝔽₂`) by explicit curves, counted by `decide`;
* `p ∣ t`, `t² ≤ 4p` forces `t = 0`, or `p ∈ {2, 3}` and `t = ±p`. -/

open LefebvreVariations

open WeierstrassCurve

private def ptEquiv {F : Type*} [Field F] (W : WeierstrassCurve F) [W.IsElliptic] :
    W.toAffine.Point ≃ Option {xy : F × F // W.toAffine.Equation xy.1 xy.2} where
  toFun
    | .zero => none
    | .some x y h => some ⟨(x, y), h.1⟩
  invFun
    | none => .zero
    | some xy => .some xy.1.1 xy.1.2 ((W.toAffine.equation_iff_nonsingular).1 xy.2)
  left_inv := by rintro (_ | _) <;> rfl
  right_inv := by rintro (_ | ⟨⟨x, y⟩, h⟩) <;> rfl

private lemma card_point_eq {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (W : WeierstrassCurve F) [W.IsElliptic] :
    Nat.card W.toAffine.Point = (Finset.univ.filter (fun xy : F × F =>
      xy.2 ^ 2 + W.a₁ * xy.1 * xy.2 + W.a₃ * xy.2 =
        xy.1 ^ 3 + W.a₂ * xy.1 ^ 2 + W.a₄ * xy.1 + W.a₆)).card + 1 := by
  classical
  rw [Nat.card_congr (ptEquiv W), Nat.card_eq_fintype_card, Fintype.card_option,
    Fintype.card_subtype]
  congr 2
  ext xy
  simp [WeierstrassCurve.Affine.equation_iff]


private lemma card_filter_sq {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) (f : F → F) :
    ((Finset.univ.filter (fun xy : F × F => xy.2 ^ 2 = f xy.1)).card : ℤ) =
      Fintype.card F + ∑ x : F, quadraticChar F (f x) := by
  rw [Finset.card_filter, Fintype.sum_prod_type]
  push_cast
  have h : ∀ x : F, (∑ y : F, if y ^ 2 = f x then (1 : ℤ) else 0) =
      quadraticChar F (f x) + 1 := by
    intro x
    rw [← quadraticChar_card_sqrts hF (f x), Set.toFinset_ofPred, Finset.card_filter]
    push_cast; rfl
  rw [Finset.sum_congr rfl (fun x _ => h x), Finset.sum_add_distrib]
  simp [add_comm]

private lemma card_point_short {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) (a b : F) [(WeierstrassCurve.mk 0 0 0 a b).IsElliptic] :
    (Nat.card (WeierstrassCurve.mk 0 0 0 a b).toAffine.Point : ℤ) =
      Fintype.card F + 1 + ∑ x : F, quadraticChar F (x ^ 3 + a * x + b) := by
  rw [card_point_eq]
  have := card_filter_sq hF (fun x => x ^ 3 + a * x + b)
  push_cast
  rw [← add_right_comm, ← this]
  congr 3
  ext xy
  simp

private lemma ringChar_ne_two (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) : ringChar (ZMod p) ≠ 2 := by
  rwa [ZMod.ringChar_zmod_n]

private lemma natCast_ne_zero_of_prime (p : ℕ) [Fact p.Prime] (n : ℕ) (hn : ¬ p ∣ n) :
    (n : ZMod p) ≠ 0 := by
  rwa [Ne, ZMod.natCast_eq_zero_iff]

private lemma sum_chi_three_mod_four (p : ℕ) [Fact p.Prime] (hp : p % 4 = 3) :
    ∑ x : ZMod p, quadraticChar (ZMod p) (x ^ 3 + (-1) * x + 0) = 0 := by
  have hm : quadraticChar (ZMod p) (-1) = -1 := by
    rw [quadraticChar_neg_one_iff_not_isSquare, ZMod.exists_sq_eq_neg_one_iff]
    omega
  set S := ∑ x : ZMod p, quadraticChar (ZMod p) (x ^ 3 + (-1) * x + 0) with hS
  have h : S = -S := by
    conv_lhs => rw [hS, ← Equiv.sum_comp (Equiv.neg (ZMod p))]
    rw [hS, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    have : (-x) ^ 3 + (-1) * (-x) + 0 = (-1) * (x ^ 3 + (-1) * x + 0) := by ring
    simp only [Equiv.neg_apply]
    rw [this, map_mul, hm]
    ring
  omega

private lemma cube_bijective (p : ℕ) [Fact p.Prime] (hp : p % 3 = 2) :
    Function.Bijective (fun x : ZMod p => x ^ 3) := by
  rw [← Finite.injective_iff_bijective]
  have key : ∀ x : ZMod p, (x ^ 3) ^ ((2 * p - 1) / 3) = x := by
    intro x
    have h3 : 3 * ((2 * p - 1) / 3) = p + (p - 1) := by
      have := (Fact.out : p.Prime).two_le
      omega
    rw [← pow_mul, h3, pow_add, ZMod.pow_card, ← pow_succ']
    have : p - 1 + 1 = p := by have := (Fact.out : p.Prime).two_le; omega
    rw [this, ZMod.pow_card]
  intro x y hxy
  rw [← key x, ← key y]
  simp only at hxy
  rw [hxy]

private lemma sum_chi_two_mod_three (p : ℕ) [Fact p.Prime] (hp : p % 3 = 2) (hp2 : p ≠ 2) :
    ∑ x : ZMod p, quadraticChar (ZMod p) (x ^ 3 + 0 * x + 1) = 0 := by
  have h1 : ∑ x : ZMod p, quadraticChar (ZMod p) (x ^ 3 + 0 * x + 1) =
      ∑ u : ZMod p, quadraticChar (ZMod p) (u + 1) := by
    simp only [zero_mul, add_zero]
    exact (cube_bijective p hp).sum_comp (fun u => quadraticChar (ZMod p) (u + 1))
  have h2 := Equiv.sum_comp (Equiv.addRight (1 : ZMod p)) (fun u => quadraticChar (ZMod p) u)
  simp only [Equiv.coe_addRight] at h2
  rw [h1, h2]
  exact quadraticChar_sum_zero (ringChar_ne_two p hp2)

private lemma prime_dvd_two_three (p : ℕ) [hp : Fact p.Prime] (a b : ℕ) (h : p ∣ 2 ^ a * 3 ^ b) :
    p = 2 ∨ p = 3 := by
  rcases (Nat.Prime.dvd_mul hp.out).1 h with h | h
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 (hp.out.dvd_of_dvd_pow h))
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_three).1 (hp.out.dvd_of_dvd_pow h))

private lemma curve_three_mod_four (p : ℕ) [Fact p.Prime] (hp : p % 4 = 3) :
    ∃ E : WeierstrassCurve (ZMod p), E.IsElliptic ∧ Nat.card E.toAffine.Point = p + 1 := by
  have hp2 : p ≠ 2 := by omega
  have hΔ : (WeierstrassCurve.mk 0 0 0 (-1) 0 : WeierstrassCurve (ZMod p)).Δ =
      ((2 ^ 6 : ℕ) : ZMod p) := by
    simp [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
      WeierstrassCurve.b₈]
    norm_num
  have hne : (WeierstrassCurve.mk 0 0 0 (-1) 0 : WeierstrassCurve (ZMod p)).Δ ≠ 0 := by
    rw [hΔ]
    refine natCast_ne_zero_of_prime p _ fun h => ?_
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1
      ((Fact.out : p.Prime).dvd_of_dvd_pow h))
  have : (WeierstrassCurve.mk 0 0 0 (-1) 0 : WeierstrassCurve (ZMod p)).IsElliptic :=
    ⟨isUnit_iff_ne_zero.2 hne⟩
  refine ⟨_, this, ?_⟩
  have := card_point_short (ringChar_ne_two p hp2) (-1 : ZMod p) 0
  rw [sum_chi_three_mod_four p hp, ZMod.card] at this
  omega

private lemma curve_two_mod_three (p : ℕ) [Fact p.Prime] (hp : p % 3 = 2) (hp2 : p ≠ 2) :
    ∃ E : WeierstrassCurve (ZMod p), E.IsElliptic ∧ Nat.card E.toAffine.Point = p + 1 := by
  have hΔ : (WeierstrassCurve.mk 0 0 0 0 1 : WeierstrassCurve (ZMod p)).Δ =
      -((2 ^ 4 * 3 ^ 3 : ℕ) : ZMod p) := by
    simp [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
      WeierstrassCurve.b₈]
    norm_num
  have hne : (WeierstrassCurve.mk 0 0 0 0 1 : WeierstrassCurve (ZMod p)).Δ ≠ 0 := by
    rw [hΔ, neg_ne_zero]
    refine natCast_ne_zero_of_prime p _ fun h => ?_
    rcases prime_dvd_two_three p 4 3 h with h | h <;> omega
  have : (WeierstrassCurve.mk 0 0 0 0 1 : WeierstrassCurve (ZMod p)).IsElliptic :=
    ⟨isUnit_iff_ne_zero.2 hne⟩
  refine ⟨_, this, ?_⟩
  have := card_point_short (ringChar_ne_two p hp2) (0 : ZMod p) 1
  rw [sum_chi_two_mod_three p hp hp2, ZMod.card] at this
  omega

private lemma small_curve {p : ℕ} [Fact p.Prime] (W : WeierstrassCurve (ZMod p))
    (hΔ : W.Δ ≠ 0) (n : ℕ)
    (h : (Finset.univ.filter (fun xy : ZMod p × ZMod p =>
      xy.2 ^ 2 + W.a₁ * xy.1 * xy.2 + W.a₃ * xy.2 =
        xy.1 ^ 3 + W.a₂ * xy.1 ^ 2 + W.a₄ * xy.1 + W.a₆)).card + 1 = n) :
    ∃ E : WeierstrassCurve (ZMod p), E.IsElliptic ∧ Nat.card E.toAffine.Point = n := by
  have : W.IsElliptic := ⟨isUnit_iff_ne_zero.2 hΔ⟩
  exact ⟨W, this, by rw [card_point_eq]; exact h⟩


/-- The six explicit curves over `𝔽₂` and `𝔽₃`; their discriminants and affine point counts are
checked by `decide`. -/
private lemma f2_three : ∃ E : WeierstrassCurve (ZMod 2), E.IsElliptic ∧ Nat.card E.toAffine.Point = 3 :=
  small_curve (WeierstrassCurve.mk 0 0 1 0 0) (by decide) 3 (by decide)
private lemma f2_five : ∃ E : WeierstrassCurve (ZMod 2), E.IsElliptic ∧ Nat.card E.toAffine.Point = 5 :=
  small_curve (WeierstrassCurve.mk 0 0 1 1 0) (by decide) 5 (by decide)
private lemma f2_one : ∃ E : WeierstrassCurve (ZMod 2), E.IsElliptic ∧ Nat.card E.toAffine.Point = 1 :=
  small_curve (WeierstrassCurve.mk 0 0 1 1 1) (by decide) 1 (by decide)
private lemma f3_seven : ∃ E : WeierstrassCurve (ZMod 3), E.IsElliptic ∧ Nat.card E.toAffine.Point = 7 :=
  small_curve (WeierstrassCurve.mk 0 0 0 (-1) 1) (by decide) 7 (by decide)
private lemma f3_one : ∃ E : WeierstrassCurve (ZMod 3), E.IsElliptic ∧ Nat.card E.toAffine.Point = 1 :=
  small_curve (WeierstrassCurve.mk 0 0 0 (-1) (-1)) (by decide) 1 (by decide)

private lemma supersingular (p : ℕ) [Fact p.Prime] :
    ∃ E : WeierstrassCurve (ZMod p), E.IsElliptic ∧ Nat.card E.toAffine.Point = p + 1 := by
  rcases (Fact.out : p.Prime).eq_two_or_odd with h2 | hodd
  · subst h2
    exact f2_three
  have hp2 : p ≠ 2 := by omega
  by_cases h4 : p % 4 = 3
  · exact curve_three_mod_four p h4
  by_cases h3 : p % 3 = 2
  · exact curve_two_mod_three p h3 hp2
  have h3' : p % 3 ≠ 0 := by
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Fact.out).1 (Nat.dvd_of_mod_eq_zero h)
    omega
  exact exists_supersingular_of_mod_twelve_eq_one p (by omega)

theorem solution (p : ℕ) [Fact p.Prime] (t : ℤ)
    (ht : t ^ 2 ≤ 4 * (p : ℤ)) (hpt : (p : ℤ) ∣ t) :
    ∃ E : WeierstrassCurve (ZMod p), E.IsElliptic ∧
      (p : ℤ) + 1 - (Nat.card E.toAffine.Point : ℤ) = t := by
  have conv : ∀ n : ℕ, (p : ℤ) + 1 - n = t →
      (∃ E : WeierstrassCurve (ZMod p), E.IsElliptic ∧ Nat.card E.toAffine.Point = n) →
      ∃ E : WeierstrassCurve (ZMod p), E.IsElliptic ∧
        (p : ℤ) + 1 - (Nat.card E.toAffine.Point : ℤ) = t := by
    rintro n hn ⟨E, hE, hc⟩
    exact ⟨E, hE, by rw [hc]; exact hn⟩
  obtain ⟨k, rfl⟩ := hpt
  have hp2 := (Fact.out : p.Prime).two_le
  rcases eq_or_ne k 0 with rfl | hk
  · exact conv (p + 1) (by push_cast; ring) (supersingular p)
  have hpos : (0 : ℤ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hk2 : 1 ≤ k ^ 2 := by
    have : 0 < k ^ 2 := by positivity
    omega
  have h1 : (p : ℤ) * k ^ 2 ≤ 4 := by
    have : (p : ℤ) * ((p : ℤ) * k ^ 2) ≤ (p : ℤ) * 4 := by nlinarith
    exact le_of_mul_le_mul_left this hpos
  have hp4 : (p : ℤ) ≤ 4 := by nlinarith
  have hk' : k ^ 2 ≤ 2 := by nlinarith
  have hk1 : k ≤ 1 := by nlinarith
  have hk1' : -1 ≤ k := by nlinarith
  have hp23 : p = 2 ∨ p = 3 := by
    have : p ≠ 4 := by
      rintro rfl
      exact absurd (Fact.out : (4 : ℕ).Prime) (by decide)
    omega
  rcases hp23 with rfl | rfl
  · rcases (show k = 1 ∨ k = -1 by omega) with rfl | rfl
    · exact conv 1 (by norm_num) f2_one
    · exact conv 5 (by norm_num) f2_five
  · rcases (show k = 1 ∨ k = -1 by omega) with rfl | rfl
    · exact conv 1 (by norm_num) f3_one
    · exact conv 7 (by norm_num) f3_seven
