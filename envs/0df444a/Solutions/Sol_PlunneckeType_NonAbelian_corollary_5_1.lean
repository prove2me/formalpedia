-- Prove2me | solution 1 for PlunneckeType.NonAbelian.corollary_5_1
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-15T04:03:43.62033+00:00
-- url     : https://prove2.me/submissions/3ba145a9-2af1-4739-9842-759653abb7a1

import Mathlib

open scoped Pointwise
open Finset

set_option autoImplicit false

namespace PlCex032

/-- The affine group AGL(1,17): `⟨a, b⟩` is the map `x ↦ a x + b`. -/
structure Aff where
  a : (ZMod 17)ˣ
  b : ZMod 17

theorem Aff.ext' {x y : Aff} (h1 : x.a = y.a) (h2 : x.b = y.b) : x = y := by
  cases x; cases y; simp only at h1 h2; subst h1; subst h2; rfl

instance : DecidableEq Aff := fun x y =>
  decidable_of_iff (x.a = y.a ∧ x.b = y.b)
    ⟨fun h => Aff.ext' h.1 h.2, fun h => h ▸ ⟨rfl, rfl⟩⟩

instance : Group Aff where
  mul x y := ⟨x.a * y.a, (x.a : ZMod 17) * y.b + x.b⟩
  one := ⟨1, 0⟩
  inv x := ⟨x.a⁻¹, -((x.a⁻¹ : (ZMod 17)ˣ) : ZMod 17) * x.b⟩
  mul_assoc x y z := Aff.ext' (mul_assoc _ _ _) (by
    show ((x.a * y.a : (ZMod 17)ˣ) : ZMod 17) * z.b + ((x.a : ZMod 17) * y.b + x.b)
      = (x.a : ZMod 17) * ((y.a : ZMod 17) * z.b + y.b) + x.b
    push_cast; ring)
  one_mul x := Aff.ext' (one_mul _) (by
    show ((1 : (ZMod 17)ˣ) : ZMod 17) * x.b + 0 = x.b
    simp)
  mul_one x := Aff.ext' (mul_one _) (by
    show (x.a : ZMod 17) * 0 + x.b = x.b
    simp)
  inv_mul_cancel x := Aff.ext' (inv_mul_cancel _) (by
    show ((x.a⁻¹ : (ZMod 17)ˣ) : ZMod 17) * x.b + -((x.a⁻¹ : (ZMod 17)ˣ) : ZMod 17) * x.b = 0
    ring)

theorem mul_a (x y : Aff) : (x * y).a = x.a * y.a := rfl
theorem mul_b (x y : Aff) : (x * y).b = (x.a : ZMod 17) * y.b + x.b := rfl
theorem inv_a (x : Aff) : (x⁻¹).a = x.a⁻¹ := rfl
theorem inv_b (x : Aff) : (x⁻¹).b = -((x.a⁻¹ : (ZMod 17)ˣ) : ZMod 17) * x.b := rfl

def e (p : (ZMod 17)ˣ × ZMod 17) : Aff := ⟨p.1, p.2⟩

theorem e_inj : Function.Injective e := by
  intro p q h
  have h1 : p.1 = q.1 := congrArg Aff.a h
  have h2 : p.2 = q.2 := congrArg Aff.b h
  exact Prod.ext h1 h2

/-- `S = H ∪ xH` with `H` the stabiliser of `0` and `x = ⟨1, 1⟩`. -/
@[irreducible] def S : Finset Aff := (univ ×ˢ ({0, 1} : Finset (ZMod 17))).image e
/-- `B = H`. -/
@[irreducible] def B : Finset Aff := (univ ×ˢ ({0} : Finset (ZMod 17))).image e

theorem memS (x : Aff) : x ∈ S ↔ (x.b = 0 ∨ x.b = 1) := by
  rw [S]
  constructor
  · intro hx
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
    simpa [e] using (Finset.mem_product.mp hp).2
  · intro hx
    exact Finset.mem_image.mpr ⟨(x.a, x.b), by simpa using hx, rfl⟩

theorem memB (x : Aff) : x ∈ B ↔ x.b = 0 := by
  rw [B]
  constructor
  · intro hx
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
    simpa [e] using (Finset.mem_product.mp hp).2
  · intro hx
    exact Finset.mem_image.mpr ⟨(x.a, x.b), by simp [hx], rfl⟩

theorem SB_eq : S * B = S := by
  ext x
  rw [Finset.mem_mul]
  constructor
  · rintro ⟨y, hy, z, hz, rfl⟩
    rw [memS] at hy ⊢
    rw [memB] at hz
    rw [mul_b, hz, mul_zero, zero_add]
    exact hy
  · intro hx
    refine ⟨x, hx, 1, (memB 1).mpr rfl, mul_one x⟩

theorem card_units : Fintype.card (ZMod 17)ˣ = 16 := by
  rw [ZMod.card_units_eq_totient, Nat.totient_prime (by norm_num)]

theorem cardS : #S = 32 := by
  rw [S, Finset.card_image_of_injective _ e_inj, Finset.card_product, Finset.card_univ,
    card_units, Finset.card_pair (by decide)]

theorem cardB : #B = 16 := by
  rw [B, Finset.card_image_of_injective _ e_inj, Finset.card_product, Finset.card_univ,
    card_units, Finset.card_singleton]

theorem h0 : (⟨1, 0⟩ : Aff) ∈ S := (memS (Aff.mk 1 0)).mpr (Or.inl (Eq.refl _))

theorem hone : (⟨1, 0⟩ : Aff)⁻¹ = 1 := by
  rw [inv_eq_one]; rfl

theorem key0 (p : (ZMod 17)ˣ × ZMod 17) (hy : p.2 = 0) : e p ∈ S * S⁻¹ * S * S⁻¹ := by
  have hs : (⟨p.1, 0⟩ : Aff) ∈ S := (memS _).mpr (Or.inl rfl)
  have heq : e p = (⟨p.1, 0⟩ : Aff) * (⟨1, 0⟩ : Aff)⁻¹ * (⟨1, 0⟩ : Aff) * (⟨1, 0⟩ : Aff)⁻¹ := by
    rw [hone, mul_one, mul_one]
    have h1 : (⟨1, 0⟩ : Aff) = 1 := rfl
    rw [h1, mul_one]
    exact Aff.ext' rfl hy
  rw [heq]
  exact Finset.mul_mem_mul (Finset.mul_mem_mul (Finset.mul_mem_mul hs
    (Finset.inv_mem_inv h0)) h0) (Finset.inv_mem_inv h0)

theorem key1 (p : (ZMod 17)ˣ × ZMod 17) (U : (ZMod 17)ˣ) (hU : (U : ZMod 17) = p.2) :
    e p ∈ S * S⁻¹ * S * S⁻¹ := by
  have hs1 : (⟨U, 0⟩ : Aff) ∈ S := (memS _).mpr (Or.inl rfl)
  have hs3 : (⟨U⁻¹ * p.1, 1⟩ : Aff) ∈ S := (memS _).mpr (Or.inr rfl)
  have heq : e p = (⟨U, 0⟩ : Aff) * (⟨1, 0⟩ : Aff)⁻¹ * (⟨U⁻¹ * p.1, 1⟩ : Aff)
      * (⟨1, 0⟩ : Aff)⁻¹ := by
    rw [hone, mul_one, mul_one]
    refine Aff.ext' ?_ ?_
    · rw [mul_a]
      show p.1 = U * (U⁻¹ * p.1)
      rw [mul_inv_cancel_left]
    · rw [mul_b]
      show p.2 = (U : ZMod 17) * 1 + 0
      rw [hU, mul_one, add_zero]
  rw [heq]
  exact Finset.mul_mem_mul (Finset.mul_mem_mul (Finset.mul_mem_mul hs1
    (Finset.inv_mem_inv h0)) hs3) (Finset.inv_mem_inv h0)

theorem key (p : (ZMod 17)ˣ × ZMod 17) : e p ∈ S * S⁻¹ * S * S⁻¹ := by
  by_cases hy : p.2 = 0
  · exact key0 p hy
  · have hu : IsUnit p.2 := by
      have : Fact (Nat.Prime 17) := ⟨by norm_num⟩
      exact isUnit_iff_ne_zero.mpr hy
    exact key1 p hu.unit hu.unit_spec

theorem big : 272 ≤ #(S * S⁻¹ * S * S⁻¹) := by
  have hsub : (univ : Finset ((ZMod 17)ˣ × ZMod 17)).image e ⊆ S * S⁻¹ * S * S⁻¹ :=
     Finset.image_subset_iff.mpr (fun p _ => key p)
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ e_inj, Finset.card_univ, Fintype.card_prod, card_units,
    ZMod.card] at hcard
  exact hcard

theorem refute (h : ∀ (S B : Finset Aff) (α : ℝ), B.Nonempty →
    (∀ C : Finset Aff, (#(C * S * B) : ℝ) ≤ α * #(C * S)) →
    (#(S * S⁻¹ * S * S⁻¹) : ℝ) ≤ α ^ 6 * ((#S : ℝ) / #B) ^ 3 * #S) : False := by
  have hB : B.Nonempty := ⟨⟨1, 0⟩, (memB _).mpr rfl⟩
  have hC : ∀ C : Finset Aff, (#(C * S * B) : ℝ) ≤ 1 * #(C * S) := by
    intro C
    rw [mul_assoc C S B, SB_eq, one_mul]
  have h1 := h S B 1 hB hC
  have h2 : (272 : ℝ) ≤ #(S * S⁻¹ * S * S⁻¹) := by exact_mod_cast big
  generalize #(S * S⁻¹ * S * S⁻¹) = n at h1 h2
  rw [cardS, cardB] at h1
  norm_num at h1
  have h3 : (272 : ℝ) ≤ 256 := h2.trans (by exact_mod_cast h1)
  norm_num at h3

end PlCex032

theorem solution : ¬ (∀ {G : Type} [Group G] [DecidableEq G] (S B : Finset G) (α : ℝ),
    B.Nonempty →
    (∀ C : Finset G, (#(C * S * B) : ℝ) ≤ α * #(C * S)) →
    (#(S * S⁻¹ * S * S⁻¹) : ℝ) ≤ α ^ 6 * ((#S : ℝ) / #B) ^ 3 * #S) := by
  intro h
  exact PlCex032.refute (fun S B α hB hC => h S B α hB hC)
