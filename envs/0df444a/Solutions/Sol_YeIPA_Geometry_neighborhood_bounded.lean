-- Prove2me | solution 1 for YeIPA.Geometry.neighborhood_bounded
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T12:19:25.422675+00:00
-- url     : https://prove2.me/submissions/44005693-665a-4311-81d6-69843cc55548

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

theorem g69c_AAt_unit {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (hrank : A.rank = m) :
    IsUnit (A * Aᵀ).det := by
  have hr : (A * Aᵀ).rank = m := by rw [Matrix.rank_self_mul_transpose]; exact hrank
  have htop : LinearMap.range (A * Aᵀ).mulVecLin = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [show Module.finrank ℝ (LinearMap.range (A * Aᵀ).mulVecLin) = (A * Aᵀ).rank from rfl, hr]
    simp
  have hsurj : Function.Surjective (A * Aᵀ).mulVec := LinearMap.range_eq_top.mp htop
  exact (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.mulVec_surjective_iff_isUnit.mp hsurj)

theorem g69c_y_eq {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (hrank : A.rank = m)
    (c s : Fin n → ℝ) (y : Fin m → ℝ) (hs : Aᵀ *ᵥ y + s = c) :
    y = ((A * Aᵀ)⁻¹ * A) *ᵥ (c - s) := by
  have h1 : c - s = Aᵀ *ᵥ y := by rw [← hs]; abel
  rw [h1, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (g69c_AAt_unit A hrank),
    Matrix.one_mulVec]

theorem g69c_abs_mulVec_le {m n : ℕ} (B : Matrix (Fin m) (Fin n) ℝ) (v : Fin n → ℝ) (R : ℝ)
    (hv : ∀ j, |v j| ≤ R) (i : Fin m) :
    |(B *ᵥ v) i| ≤ ∑ i', ∑ j, |B i' j| * R := by
  have h1 : |(B *ᵥ v) i| ≤ ∑ j, |B i j| * R := by
    unfold mulVec dotProduct
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun j _ => ?_))
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hv j) (abs_nonneg _)
  have hR : ∀ i', 0 ≤ ∑ j, |B i' j| * R := by
    intro i'
    by_cases hn : Nonempty (Fin n)
    · obtain ⟨j0⟩ := hn
      have : 0 ≤ R := (abs_nonneg _).trans (hv j0)
      exact Finset.sum_nonneg (fun j _ => mul_nonneg (abs_nonneg _) this)
    · simp only [not_nonempty_iff] at hn
      simp
  exact h1.trans (Finset.single_le_sum (f := fun i' => ∑ j, |B i' j| * R) (fun i' _ => hR i')
    (Finset.mem_univ i))

/-- Theorem 2.18 (i) (Ye 1997, p. 74). -/
theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (hrank : A.rank = m) (hmn : m < n)
    (hP : ∃ x, PrimalInterior A b x) (hD : ∃ y s, DualInterior A c y s)
    (nrm : (Fin n → ℝ) → ℝ) (hnrm : ∀ v, negInfNorm v ≤ nrm v)
    (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1) (μ₀ : ℝ) :
    Bornology.IsBounded {p : (Fin n → ℝ) × (Fin m → ℝ) × (Fin n → ℝ) |
      InNeighborhood A b c nrm η p.1 p.2.1 p.2.2 ∧ p.1 ⬝ᵥ p.2.2 ≤ n * μ₀} := by
  obtain ⟨x0, hx0, hx0p⟩ := hP
  obtain ⟨y0, s0, hs0, hs0p⟩ := hD
  obtain ⟨R, hR, hB⟩ := g69c_xs_bound A b c x0 y0 s0 hx0 hx0p hs0 hs0p (n * μ₀)
  set Bm := (A * Aᵀ)⁻¹ * A
  set Ry := ∑ i', ∑ j, |Bm i' j| * (‖c‖ + R)
  have hRy : 0 ≤ Ry := Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ =>
    mul_nonneg (abs_nonneg _) (add_nonneg (norm_nonneg _) hR)))
  rw [isBounded_iff_forall_norm_le]
  refine ⟨max R Ry, ?_⟩
  rintro ⟨x, y, s⟩ ⟨⟨⟨hx, hxp⟩, ⟨hs, hsp⟩, _⟩, hxs⟩
  have H := hB x y s hx (fun j => (hxp j).le) hs (fun j => (hsp j).le) hxs
  have hM : 0 ≤ max R Ry := le_max_of_le_left hR
  rw [norm_prod_le_iff, norm_prod_le_iff]
  refine ⟨?_, ?_, ?_⟩
  · rw [pi_norm_le_iff_of_nonneg hM]; intro j; rw [Real.norm_eq_abs]
    exact (H j).1.trans (le_max_left _ _)
  · rw [pi_norm_le_iff_of_nonneg hM]; intro i; rw [Real.norm_eq_abs]
    rw [g69c_y_eq A hrank c s y hs]
    refine (g69c_abs_mulVec_le Bm (c - s) (‖c‖ + R) (fun j => ?_) i).trans (le_max_right _ _)
    rw [Pi.sub_apply]
    refine (abs_sub _ _).trans (add_le_add ?_ (H j).2)
    rw [← Real.norm_eq_abs]; exact norm_le_pi_norm c j
  · rw [pi_norm_le_iff_of_nonneg hM]; intro j; rw [Real.norm_eq_abs]
    exact (H j).2.trans (le_max_left _ _)
