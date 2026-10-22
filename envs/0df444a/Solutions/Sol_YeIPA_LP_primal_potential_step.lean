-- Prove2me | solution 1 for YeIPA.LP.primal_potential_step
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T14:44:35.073676+00:00
-- url     : https://prove2.me/submissions/6228452f-eb4b-49f8-83c9-5a005332bc70

import Mathlib
import Definitions.Def_YeIPA_LP_PotentialReduction

open Matrix
open YeIPA.LP
open YeIPA.LP

theorem g70ye_gap {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x : Fin n → ℝ) (y : Fin m → ℝ) (s : Fin n → ℝ) (hx : A *ᵥ x = b)
    (hs : Aᵀ *ᵥ y + s = c) : c ⬝ᵥ x = b ⬝ᵥ y + x ⬝ᵥ s := by
  rw [← hs, ← hx, add_dotProduct, mulVec_transpose, ← dotProduct_mulVec, dotProduct_comm s x,
    dotProduct_comm (A *ᵥ x) y]

theorem g70ye_log_term {d r : ℝ} (hd : |d| ≤ r) (hr : r < 1) :
    d - d ^ 2 / (2 * (1 - r)) ≤ Real.log (1 + d) := by
  have hr0 : 0 ≤ r := le_trans (abs_nonneg _) hd
  have h1r : 0 < 1 - r := by linarith
  rcases le_total 0 d with h | h
  · -- x = d/(2+d)
    set x := d / (2 + d) with hx
    have hx0 : 0 ≤ x := by positivity
    have hx1 : x < 1 := by rw [hx, div_lt_one (by linarith)]; linarith
    have key := Real.sum_range_le_log_div hx0 hx1 1
    simp only [Finset.sum_range_one, mul_zero, zero_add, pow_one, Nat.cast_zero] at key
    have he : (1 + x) / (1 - x) = 1 + d := by
      rw [hx]; field_simp; ring
    rw [he] at key
    have hsq : d - d ^ 2 / (2 * (1 - r)) ≤ d - d ^ 2 / 2 := by
      have : d ^ 2 / 2 ≤ d ^ 2 / (2 * (1 - r)) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity); nlinarith
      linarith
    have h2 : d - d ^ 2 / 2 ≤ 2 * x := by
      rw [hx]; rw [show 2 * (d / (2 + d)) = 2 * d / (2 + d) by ring, le_div_iff₀ (by linarith)]
      nlinarith [sq_nonneg d, mul_nonneg h (sq_nonneg d)]
    linarith
  · have hd' : -d ≤ r := by rw [abs_of_nonpos h] at hd; exact hd
    have hu : 0 < 1 + d := by linarith
    set u := 1 + d with hu'
    have hu0 : u ≠ 0 := hu.ne'
    have hu1 : 1 + u ≠ 0 := by linarith
    set x := (1 - u) / (1 + u) with hx
    have hx0 : 0 ≤ x := by apply div_nonneg <;> linarith
    have hx1 : x < 1 := by rw [hx, div_lt_one (by linarith)]; linarith
    have key := Real.log_div_le_sum_range_add hx0 hx1 0
    clear_value x u
    simp only [Finset.range_zero, Finset.sum_empty, zero_add, mul_zero, pow_one] at key
    have h1x : 1 - x ≠ 0 := by linarith
    have h1x2 : 1 - x ^ 2 ≠ 0 := by nlinarith
    have he : (1 + x) / (1 - x) = u⁻¹ := by
      rw [div_eq_iff h1x, hx]; field_simp; ring
    have he2 : x / (1 - x ^ 2) = (u⁻¹ - u) / 4 := by
      rw [div_eq_iff h1x2, hx]; field_simp; ring
    rw [he, he2, Real.log_inv] at key
    have h3 : d - d ^ 2 / (2 * (1 - r)) ≤ d - d ^ 2 / (2 * u) := by
      have : d ^ 2 / (2 * u) ≤ d ^ 2 / (2 * (1 - r)) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity); linarith
      linarith
    have h4 : d - d ^ 2 / (2 * u) = - (2 * ((u⁻¹ - u) / 4)) := by
      have : (1 + d) ≠ 0 := by linarith
      rw [hu']; field_simp; ring
    linarith

theorem g70ye_AAt_unit {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (hrank : A.rank = m) :
    IsUnit (A * Aᵀ).det := by
  have hr : (A * Aᵀ).rank = m := by rw [Matrix.rank_self_mul_transpose]; exact hrank
  have htop : LinearMap.range (A * Aᵀ).mulVecLin = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [show Module.finrank ℝ (LinearMap.range (A * Aᵀ).mulVecLin) = (A * Aᵀ).rank from rfl, hr]
    simp
  have hsurj : Function.Surjective (A * Aᵀ).mulVec := LinearMap.range_eq_top.mp htop
  exact (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.mulVec_surjective_iff_isUnit.mp hsurj)


theorem g70ye_proj {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (hr : A.rank = m) (x : Fin n → ℝ)
    (hx : ∀ j, 0 < x j) (g p : Fin n → ℝ)
    (hp : p = (1 - diagonal x * Aᵀ * (A * diagonal x * diagonal x * Aᵀ)⁻¹ * A * diagonal x) *ᵥ g) :
    A *ᵥ (diagonal x *ᵥ p) = 0 ∧ p ⬝ᵥ g = p ⬝ᵥ p := by
  set B := A * diagonal x with hBdef
  have hdet : IsUnit (diagonal x).det := by
    rw [det_diagonal]; exact (Finset.prod_pos fun i _ => hx i).ne'.isUnit
  have hrB : B.rank = m := by rw [hBdef, rank_mul_eq_left_of_isUnit_det _ _ hdet, hr]
  have hU := g70ye_AAt_unit B hrB
  have hBt : Bᵀ = diagonal x * Aᵀ := by simp [B, transpose_mul, diagonal_transpose]
  have hM : A * diagonal x * diagonal x * Aᵀ = B * Bᵀ := by
    rw [hBt]; simp only [B, Matrix.mul_assoc]
  have hPm : diagonal x * Aᵀ * (A * diagonal x * diagonal x * Aᵀ)⁻¹ * A * diagonal x =
      Bᵀ * (B * Bᵀ)⁻¹ * B := by
    rw [hM, hBt]; simp only [B, Matrix.mul_assoc]
  set w := (B * Bᵀ)⁻¹ *ᵥ (B *ᵥ g)
  have hp' : p = g - Bᵀ *ᵥ w := by
    rw [hp, hPm, sub_mulVec, one_mulVec]; simp only [w, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have hBp : B *ᵥ p = 0 := by
    rw [hp', mulVec_sub, mulVec_mulVec]
    rw [show (B * Bᵀ) *ᵥ w = B *ᵥ g by
      simp only [w, mulVec_mulVec]; rw [← Matrix.mul_assoc, mul_nonsing_inv _ hU, Matrix.one_mul],
      sub_self]
  have orth : p ⬝ᵥ (Bᵀ *ᵥ w) = (B *ᵥ p) ⬝ᵥ w := by
    rw [mulVec_transpose, dotProduct_comm, dotProduct_comm (B *ᵥ p), dotProduct_mulVec]
  refine ⟨by rw [mulVec_mulVec]; exact hBp, ?_⟩
  have hg' : g = p + Bᵀ *ᵥ w := by rw [hp']; abel
  rw [hg', dotProduct_add, orth, hBp, zero_dotProduct, add_zero]


/-- Ye 1997, p. 122, the display following (4.10). Under the standing assumptions (p. 63), let
`(xᵏ, yᵏ, sᵏ) ∈ F̊`, `ρ = √n` (§4.3, p. 121), `zᵏ = bᵀyᵏ`, `0 < α < 1`, and let `xᵏ⁺¹` be the
step (4.10). Then `P_{n+ρ}(xᵏ⁺¹, zᵏ) − P_{n+ρ}(xᵏ, zᵏ) ≤ −α‖pᵏ‖ + α²/(2(1 − α))`. -/
theorem solution {m n : ℕ} (hn : 0 < n) (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) (hA : StandingAssumptions A b c)
    (x : Fin n → ℝ) (y : Fin m → ℝ) (s : Fin n → ℝ) (hF : IsInteriorFeasible A b c x y s)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    primalPotential (Real.sqrt n) c (primalStep A c (Real.sqrt n) α x (b ⬝ᵥ y)) (b ⬝ᵥ y) -
        primalPotential (Real.sqrt n) c x (b ⬝ᵥ y) ≤
      -α * norm2 (pVec A c (Real.sqrt n) x (b ⬝ᵥ y)) + α ^ 2 / (2 * (1 - α)) := by
  obtain ⟨hAx, hx, hAy, hs⟩ := hF
  set z := b ⬝ᵥ y with hz
  set ρ := Real.sqrt n with hρ
  obtain ⟨p, hpdef⟩ : ∃ p, pVec A c ρ x z = p := ⟨_, rfl⟩
  obtain ⟨N, hNdef⟩ : ∃ N, norm2 p = N := ⟨_, rfl⟩
  rw [hpdef, hNdef]
  set K : ℝ := (n : ℝ) + ρ with hK
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hK0 : 0 < K := by positivity
  have hxs : 0 < x ⬝ᵥ s := by
    have j : Fin n := ⟨0, hn⟩
    exact Finset.sum_pos (fun i _ => mul_pos (hx i) (hs i)) ⟨j, Finset.mem_univ j⟩
  have hF : 0 < c ⬝ᵥ x - z := by rw [g70ye_gap A b c x y s hAx hAy]; linarith
  have hN0 : 0 ≤ N := hNdef ▸ Real.sqrt_nonneg _
  have h1α : 0 < 1 - α := by linarith
  rcases hN0.eq_or_lt with hN | hN
  · have : primalStep A c ρ α x z = x := by
      funext j; simp only [primalStep, hpdef, hNdef, ← hN, div_zero, sub_zero]
    rw [this, ← hN]; simp only [sub_self, mul_zero, zero_add]; positivity
  set d : Fin n → ℝ := fun j => -α * p j / N with hd
  have hstep : ∀ j, primalStep A c ρ α x z j = x j * (1 + d j) := by
    intro j; simp only [primalStep, hd, hpdef, hNdef]; field_simp; ring
  have hpN : ∀ j, |p j| ≤ N := fun j => hNdef ▸ Real.abs_le_sqrt (Finset.single_le_sum
    (f := fun i => p i ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ j))
  have hdα : ∀ j, |d j| ≤ α := by
    intro j; simp only [hd]
    rw [abs_div, abs_mul, abs_neg, abs_of_pos hα0, abs_of_pos hN, div_le_iff₀ hN]
    exact mul_le_mul_of_nonneg_left (hpN j) hα0.le
  have hd1 : ∀ j, 0 < 1 + d j := fun j => by
    have := (abs_le.1 (hdα j)).1; linarith
  have hN2 : ∑ j, p j ^ 2 = N ^ 2 := by
    rw [← hNdef, norm2, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  have hsumd2 : ∑ j, d j ^ 2 = α ^ 2 := by
    simp only [hd, div_pow, mul_pow, neg_sq]
    rw [← Finset.sum_div, ← Finset.mul_sum, hN2]; field_simp
  -- the new point is feasible
  obtain ⟨xp, hxp⟩ : ∃ xp, primalStep A c ρ α x z = xp := ⟨_, rfl⟩
  rw [hxp]
  have hstep' : ∀ j, xp j = x j * (1 + d j) := fun j => by rw [← hxp, hstep j]
  have hxp_eq : xp = x - (α / N) • (diagonal x *ᵥ p) := by
    funext j; rw [hstep' j]; simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      mulVec_diagonal, hd]; field_simp; ring
  obtain ⟨hproj1, hproj2⟩ := g70ye_proj A hA.1 x hx
    (diagonal x *ᵥ gradPrimalPotential ρ c x z) p (by rw [← hpdef]; rfl)
  have hAxp : A *ᵥ xp = b := by
    rw [hxp_eq, mulVec_sub, mulVec_smul, hproj1, smul_zero, sub_zero, hAx]
  have hxpp : ∀ j, 0 < xp j := fun j => by rw [hstep' j]; exact mul_pos (hx j) (hd1 j)
  have hFp : 0 < c ⬝ᵥ xp - z := by
    rw [g70ye_gap A b c xp y s hAxp hAy]
    have : 0 < xp ⬝ᵥ s := by
      have j : Fin n := ⟨0, hn⟩
      exact Finset.sum_pos (fun i _ => mul_pos (hxpp i) (hs i)) ⟨j, Finset.mem_univ j⟩
    linarith
  -- potential difference
  have hdiff : primalPotential ρ c xp z - primalPotential ρ c x z =
      K * Real.log ((c ⬝ᵥ xp - z) / (c ⬝ᵥ x - z)) - ∑ j, Real.log (1 + d j) := by
    unfold primalPotential
    rw [Real.log_div hFp.ne' hF.ne']
    have : ∑ j, Real.log (xp j) = ∑ j, Real.log (x j) + ∑ j, Real.log (1 + d j) := by
      rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro j _
      rw [hstep' j, Real.log_mul (hx j).ne' (hd1 j).ne']
    rw [this]; ring
  have hlog1 : Real.log ((c ⬝ᵥ xp - z) / (c ⬝ᵥ x - z)) ≤ (c ⬝ᵥ xp - z) / (c ⬝ᵥ x - z) - 1 :=
    Real.log_le_sub_one_of_pos (div_pos hFp hF)
  have hlog2 : ∑ j, (d j - d j ^ 2 / (2 * (1 - α))) ≤ ∑ j, Real.log (1 + d j) :=
    Finset.sum_le_sum fun j _ => g70ye_log_term (hdα j) hα1
  have hsplit2 : ∑ j, (d j - d j ^ 2 / (2 * (1 - α))) = ∑ j, d j - α ^ 2 / (2 * (1 - α)) := by
    have : ∑ j, d j ^ 2 / (2 * (1 - α)) = α ^ 2 / (2 * (1 - α)) := by
      rw [← Finset.sum_div, hsumd2]
    rw [Finset.sum_sub_distrib, this]
  -- the key identity
  have hg : ∀ j, (diagonal x *ᵥ gradPrimalPotential ρ c x z) j =
      K / (c ⬝ᵥ x - z) * (c j * x j) - 1 := by
    intro j; rw [mulVec_diagonal]; simp only [gradPrimalPotential]
    rw [← hK]; field_simp
    rw [mul_sub, mul_div_cancel₀ _ (hx j).ne']; ring
  have hkey : K * ((c ⬝ᵥ xp - z) / (c ⬝ᵥ x - z) - 1) - ∑ j, d j = -α * N := by
    have e1 : (c ⬝ᵥ xp - z) / (c ⬝ᵥ x - z) - 1 = (∑ j, c j * x j * d j) / (c ⬝ᵥ x - z) := by
      rw [div_sub_one hF.ne']; congr 1
      simp only [dotProduct]; rw [sub_sub_sub_cancel_right, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro j _; rw [hstep' j]; ring
    have e2 : K * ((∑ j, c j * x j * d j) / (c ⬝ᵥ x - z)) - ∑ j, d j =
        -(α / N) * (p ⬝ᵥ (diagonal x *ᵥ gradPrimalPotential ρ c x z)) := by
      simp only [dotProduct, hg, hd, Finset.mul_sum, Finset.sum_div, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro j _; field_simp; ring
    rw [e1, e2, hproj2]
    have : p ⬝ᵥ p = N ^ 2 := by rw [← hN2]; simp only [dotProduct]; congr 1; funext j; ring
    rw [this]; field_simp
  rw [hdiff]
  have := mul_le_mul_of_nonneg_left hlog1 hK0.le
  linarith



