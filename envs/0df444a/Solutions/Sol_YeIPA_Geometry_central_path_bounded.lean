-- Prove2me | solution 1 for YeIPA.Geometry.central_path_bounded
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T12:15:07.534986+00:00
-- url     : https://prove2.me/submissions/92f56f20-a8d3-436d-b6ec-b0153ab7b468

import Mathlib
import Definitions.Def_YeIPA_Geometry_CentralPath

open Matrix
open YeIPA.Geometry

theorem g69c_gap {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x : Fin n → ℝ) (y : Fin m → ℝ) (s : Fin n → ℝ) (hx : A *ᵥ x = b)
    (hs : Aᵀ *ᵥ y + s = c) : c ⬝ᵥ x = b ⬝ᵥ y + x ⬝ᵥ s := by
  rw [← hs, ← hx, add_dotProduct, mulVec_transpose, ← dotProduct_mulVec, dotProduct_comm s x,
    dotProduct_comm (A *ᵥ x) y]

theorem g69c_nonneg_dot {n : ℕ} (x s : Fin n → ℝ) (hx : ∀ j, 0 ≤ x j) (hs : ∀ j, 0 ≤ s j)
    (j : Fin n) : x j * s j ≤ x ⬝ᵥ s := by
  unfold dotProduct
  exact Finset.single_le_sum (f := fun i => x i * s i) (fun i _ => mul_nonneg (hx i) (hs i))
    (Finset.mem_univ j)

theorem g69c_dot_nonneg {n : ℕ} (x s : Fin n → ℝ) (hx : ∀ j, 0 ≤ x j) (hs : ∀ j, 0 ≤ s j) :
    0 ≤ x ⬝ᵥ s := Finset.sum_nonneg (fun j _ => mul_nonneg (hx j) (hs j))

/-- coordinate bound for feasible pairs with bounded gap -/
theorem g69c_xs_bound {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x0 : Fin n → ℝ) (y0 : Fin m → ℝ) (s0 : Fin n → ℝ) (hx0 : A *ᵥ x0 = b)
    (hx0p : ∀ j, 0 < x0 j) (hs0 : Aᵀ *ᵥ y0 + s0 = c) (hs0p : ∀ j, 0 < s0 j) (K : ℝ) :
    ∃ R, 0 ≤ R ∧ ∀ (x : Fin n → ℝ) (y : Fin m → ℝ) (s : Fin n → ℝ), A *ᵥ x = b →
      (∀ j, 0 ≤ x j) → Aᵀ *ᵥ y + s = c → (∀ j, 0 ≤ s j) → x ⬝ᵥ s ≤ K →
      ∀ j, |x j| ≤ R ∧ |s j| ≤ R := by
  set L := |K| + x0 ⬝ᵥ s0
  have hL : 0 ≤ L := add_nonneg (abs_nonneg K)
    (g69c_dot_nonneg x0 s0 (fun j => (hx0p j).le) (fun j => (hs0p j).le))
  set T := ∑ j, (1 / s0 j + 1 / x0 j)
  have hT : ∀ j, 1 / s0 j ≤ T ∧ 1 / x0 j ≤ T := by
    intro j
    have h1 : 1 / s0 j + 1 / x0 j ≤ T :=
      Finset.single_le_sum (f := fun j => 1 / s0 j + 1 / x0 j)
        (fun i _ => add_nonneg (by have := hs0p i; positivity) (by have := hx0p i; positivity))
        (Finset.mem_univ j)
    have := hs0p j; have := hx0p j
    have a1 : 0 ≤ 1 / s0 j := by positivity
    have a2 : 0 ≤ 1 / x0 j := by positivity
    constructor <;> linarith
  have hT0 : 0 ≤ T := Finset.sum_nonneg (fun i _ =>
    add_nonneg (by have := hs0p i; positivity) (by have := hx0p i; positivity))
  refine ⟨L * T, mul_nonneg hL hT0, ?_⟩
  intro x y s hx hxn hs hsn hK j
  have e1 := g69c_gap A b c x y s hx hs
  have e2 := g69c_gap A b c x0 y0 s0 hx0 hs0
  have e3 := g69c_gap A b c x y0 s0 hx hs0
  have e4 := g69c_gap A b c x0 y s hx0 hs
  have hid : x ⬝ᵥ s0 + x0 ⬝ᵥ s = x ⬝ᵥ s + x0 ⬝ᵥ s0 := by linarith
  have d1 := g69c_dot_nonneg x0 s (fun j => (hx0p j).le) hsn
  have d2 := g69c_dot_nonneg x s0 hxn (fun j => (hs0p j).le)
  have hKa := le_abs_self K
  have b1 := g69c_nonneg_dot x s0 hxn (fun j => (hs0p j).le) j
  have b2 := g69c_nonneg_dot x0 s (fun j => (hx0p j).le) hsn j
  have hx1 : x j * s0 j ≤ L := by linarith
  have hs1 : x0 j * s j ≤ L := by linarith
  have hsj := hs0p j
  have hxj := hx0p j
  obtain ⟨t1, t2⟩ := hT j
  rw [abs_of_nonneg (hxn j), abs_of_nonneg (hsn j)]
  constructor
  · have : x j ≤ L * (1 / s0 j) := by
      rw [mul_one_div, le_div_iff₀ hsj]; exact hx1
    exact this.trans (mul_le_mul_of_nonneg_left t1 hL)
  · have : s j ≤ L * (1 / x0 j) := by
      rw [mul_one_div, le_div_iff₀ hxj]; linarith
    exact this.trans (mul_le_mul_of_nonneg_left t2 hL)

/-- Theorem 2.17 (i) (Ye 1997, p. 72). -/
theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (hrank : A.rank = m) (hmn : m < n)
    (hP : ∃ x, PrimalInterior A b x) (hD : ∃ y s, DualInterior A c y s)
    (μ₀ : ℝ) (hμ₀ : 0 < μ₀) :
    Bornology.IsBounded {p : (Fin n → ℝ) × (Fin n → ℝ) |
      ∃ μ : ℝ, 0 < μ ∧ μ ≤ μ₀ ∧ ∃ y : Fin m → ℝ, IsCentralPathPoint A b c μ p.1 y p.2} := by
  obtain ⟨x0, hx0, hx0p⟩ := hP
  obtain ⟨y0, s0, hs0, hs0p⟩ := hD
  obtain ⟨R, hR, hB⟩ := g69c_xs_bound A b c x0 y0 s0 hx0 hx0p hs0 hs0p (n * μ₀)
  rw [isBounded_iff_forall_norm_le]
  refine ⟨R, ?_⟩
  rintro ⟨x, s⟩ ⟨μ, hμ, hμle, y, ⟨hx, hxp⟩, ⟨hs, hsp⟩, hc⟩
  have hxs : x ⬝ᵥ s ≤ n * μ₀ := by
    have : x ⬝ᵥ s = n * μ := by
      unfold dotProduct; simp only [hc, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
    rw [this]; exact mul_le_mul_of_nonneg_left hμle (Nat.cast_nonneg n)
  have H := hB x y s hx (fun j => (hxp j).le) hs (fun j => (hsp j).le) hxs
  rw [norm_prod_le_iff]
  constructor
  · rw [pi_norm_le_iff_of_nonneg hR]; intro j; rw [Real.norm_eq_abs]; exact (H j).1
  · rw [pi_norm_le_iff_of_nonneg hR]; intro j; rw [Real.norm_eq_abs]; exact (H j).2
