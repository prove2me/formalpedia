-- Prove2me | solution 1 for StableSKC.Galois.scale_round_formula
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-22T17:55:44.263859+00:00
-- url     : https://prove2.me/submissions/3adf1a2c-2d62-4f7b-8a2b-fb00fe027108

import Mathlib
import Definitions.Def_StableSKC_Galois_Model

set_option autoImplicit false

open StableSKC.Galois

private theorem round_unique {k : ℕ} {P : Type*} (T : Seeding k P) (x y : P)
    {i j : ℕ} (hi : CanMeetIn T x y i) (hj : CanMeetIn T x y j) : i = j := by
  have no_lt {a b : ℕ} (ha : CanMeetIn T x y a) (hb : CanMeetIn T x y b)
      (hab : a < b) : False := by
    have hexp : a + (b - 1 - a) = b - 1 := by omega
    have hsame := congrArg (fun n : ℕ => n / 2 ^ (b - 1 - a)) ha.2.2.1
    rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, ← pow_add, hexp] at hsame
    exact hb.2.2.2 hsame
  rcases lt_trichotomy i j with hij | hij | hij
  · exact False.elim (no_lt hi hj hij)
  · exact hij
  · exact False.elim (no_lt hj hi hij)

private theorem deg_neg {F : Type*} [Field F] [Algebra (ZMod 2) F]
    (pb : PowerBasis (ZMod 2) F) (x : F) : deg pb (-x) = deg pb x := by
  classical
  simp [deg]

theorem solution {F : Type*} [Field F] [Algebra (ZMod 2) F]
    (pb : PowerBasis (ZMod 2) F) (T : Seeding pb.dim F)
    (hT : ∀ x y : F, x ≠ y → CanMeetIn T x y (1 + deg pb (x - y))) (z : Fˣ) :
    (∀ x y : F, x ≠ y → ∀ i : ℕ,
      (CanMeetIn (scale T z) x y i ↔ CanMeetIn (scale T z) 0 (x - y) i)) ∧
    (∀ y : F, y ≠ 0 → ∀ i : ℕ,
      (CanMeetIn (scale T z) 0 y i ↔ i = 1 + deg pb ((↑z⁻¹ : F) * y))) := by
  have transport (x y : F) (i : ℕ) :
      CanMeetIn (scale T z) x y i ↔ CanMeetIn T ((↑z⁻¹ : F) * x) ((↑z⁻¹ : F) * y) i :=
    Iff.rfl
  have original (x y : F) (hxy : x ≠ y) (i : ℕ) :
      CanMeetIn T x y i ↔ i = 1 + deg pb (x - y) := by
    constructor
    · intro hi
      exact round_unique T x y hi (hT x y hxy)
    · rintro rfl
      exact hT x y hxy
  have scaled (x y : F) (hxy : x ≠ y) (i : ℕ) :
      CanMeetIn (scale T z) x y i ↔ i = 1 + deg pb ((↑z⁻¹ : F) * (x - y)) := by
    rw [transport, original _ _ ((mul_right_injective₀ (Units.ne_zero z⁻¹)).ne hxy)]
    rw [mul_sub]
  constructor
  · intro x y hxy i
    rw [scaled x y hxy i, scaled 0 (x - y) (Ne.symm (sub_ne_zero.mpr hxy)) i]
    simp only [zero_sub, mul_neg, deg_neg]
  · intro y hy i
    rw [scaled 0 y (Ne.symm hy) i]
    simp only [zero_sub, mul_neg, deg_neg]
