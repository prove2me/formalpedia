-- Prove2me | solution 1 for YeIPA.LP.pd_potential_reduction
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T15:48:34.171526+00:00
-- url     : https://prove2.me/submissions/c729e48b-2fcb-4771-bb65-487210a95ebf

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

theorem g70ye_pstep {m n : ℕ} (hn : 0 < n) (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) (hA : StandingAssumptions A b c)
    (x : Fin n → ℝ) (y : Fin m → ℝ) (s : Fin n → ℝ) (hF : IsInteriorFeasible A b c x y s)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    (∀ j, 0 < primalStep A c (Real.sqrt n) α x (b ⬝ᵥ y) j) ∧
    A *ᵥ primalStep A c (Real.sqrt n) α x (b ⬝ᵥ y) = b ∧
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
    rw [this]; refine ⟨hx, hAx, ?_⟩
    rw [← hN]; simp only [sub_self, mul_zero, zero_add]; positivity
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
  refine ⟨hxpp, hAxp, ?_⟩
  rw [hdiff]
  have := mul_le_mul_of_nonneg_left hlog1 hK0.le
  linarith

theorem g70ye_smallp {m n : ℕ} (hn : 0 < n) (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) (hA : StandingAssumptions A b c)
    (x : Fin n → ℝ) (y : Fin m → ℝ) (s : Fin n → ℝ) (hF : IsInteriorFeasible A b c x y s)
    (η : ℝ)
    (hp : norm2 (pVec A c (Real.sqrt n) x (b ⬝ᵥ y)) <
      min (η * Real.sqrt (n / (n + η ^ 2))) (1 - η)) :
    (∀ j, 0 < sOf A b c (Real.sqrt n) x (b ⬝ᵥ y) j) ∧
      norm2 (fun j => x j * sOf A b c (Real.sqrt n) x (b ⬝ᵥ y) j
          - x ⬝ᵥ sOf A b c (Real.sqrt n) x (b ⬝ᵥ y) / n) <
        η * (x ⬝ᵥ sOf A b c (Real.sqrt n) x (b ⬝ᵥ y) / n) ∧
      x ⬝ᵥ sOf A b c (Real.sqrt n) x (b ⬝ᵥ y) / n <
        (1 - η / (2 * Real.sqrt n)) * (x ⬝ᵥ s / n) := by
  obtain ⟨hAx, hx, hAy, hs⟩ := hF
  set z := b ⬝ᵥ y with hz
  set ρ := Real.sqrt n with hρ
  set K : ℝ := (n : ℝ) + ρ with hK
  set Δ := c ⬝ᵥ x - z with hΔ
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hr1 : 1 ≤ ρ := by rw [hρ]; exact Real.one_le_sqrt.2 (by exact_mod_cast hn)
  have hr2 : ρ ^ 2 = n := Real.sq_sqrt hn'.le
  have hK0 : 0 < K := by positivity
  have hxs : 0 < x ⬝ᵥ s := by
    have j : Fin n := ⟨0, hn⟩
    exact Finset.sum_pos (fun i _ => mul_pos (hx i) (hs i)) ⟨j, Finset.mem_univ j⟩
  have hgap : Δ = x ⬝ᵥ s := by rw [hΔ, g70ye_gap A b c x y s hAx hAy]; ring
  have hΔ0 : 0 < Δ := hgap ▸ hxs
  set S := sOf A b c ρ x z with hS
  set p := pVec A c ρ x z with hp
  set t : ℝ := K / Δ with ht
  have ht0 : 0 < t := div_pos hK0 hΔ0
  -- p_j = t x_j S_j - 1
  have hpj : ∀ j, p j = t * (x j * S j) - 1 := by
    have hg : diagonal x *ᵥ gradPrimalPotential ρ c x z = t • (diagonal x *ᵥ c) - ones n := by
      funext j; simp only [mulVec_diagonal, gradPrimalPotential, Pi.sub_apply, Pi.smul_apply,
        smul_eq_mul, ones]
      rw [← hK, ← hΔ, ← ht, mul_sub, mul_inv_cancel₀ (hx j).ne']; ring
    have hxe : diagonal x *ᵥ ones n = x := by funext j; simp [mulVec_diagonal, ones]
    have hyOf : t • yOf A b c ρ x z = t • yTwo A c x - yOne A b x := by
      simp only [yOf, smul_sub, smul_smul]
      rw [← hK, ← hΔ, show t * (Δ / K) = 1 by rw [ht]; field_simp, one_smul]
    have hP : (diagonal x * Aᵀ * (A * diagonal x * diagonal x * Aᵀ)⁻¹ * A * diagonal x) *ᵥ
        (diagonal x *ᵥ gradPrimalPotential ρ c x z) =
        diagonal x *ᵥ (Aᵀ *ᵥ (t • yOf A b c ρ x z)) := by
      simp only [← mulVec_mulVec]
      rw [hg, mulVec_sub, mulVec_smul, hxe, mulVec_sub, mulVec_smul, hAx, mulVec_sub,
        mulVec_smul, hyOf]
      rfl
    intro j
    rw [hp]; unfold pVec
    rw [sub_mulVec, one_mulVec, hP, hg]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mulVec_diagonal, ones, mulVec_smul, hS,
      sOf]
    ring
  set N := norm2 p with hN
  have hN0 : 0 ≤ N := Real.sqrt_nonneg _
  have hpN : ∀ j, |p j| ≤ N := fun j => Real.abs_le_sqrt (Finset.single_le_sum
    (f := fun i => p i ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ j))
  have hq : ∑ j, p j ^ 2 = N ^ 2 := by
    rw [hN, norm2, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  have hp1 := lt_of_lt_of_le hp (min_le_right _ _)
  have hp2 := lt_of_lt_of_le hp (min_le_left _ _)
  have hη : 0 < η := by
    by_contra h; push_neg at h
    have : η * Real.sqrt (n / (n + η ^ 2)) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg h (Real.sqrt_nonneg _)
    linarith
  have hN1 : N < 1 := by linarith
  -- positivity of S
  have hSpos : ∀ j, 0 < S j := by
    intro j
    have h1 : 0 < t * (x j * S j) := by
      have := (abs_le.1 (hpN j)).1; rw [hpj j] at this; linarith
    have h2 : 0 < x j * S j := pos_of_mul_pos_right h1 ht0.le
    exact pos_of_mul_pos_right h2 (hx j).le
  -- means
  set a : ℝ := (∑ j, p j) / n with ha
  have hsum_p : ∑ j, p j = n * a := by rw [ha]; field_simp
  have hmu : t * (x ⬝ᵥ S / n) = 1 + a := by
    have : t * (x ⬝ᵥ S) = n + ∑ j, p j := by
      simp only [dotProduct, Finset.mul_sum, hpj, Finset.sum_sub_distrib]; simp
    rw [mul_div_assoc', this, ha]; field_simp
  have hcs : (∑ j, p j) ^ 2 ≤ n * N ^ 2 := by
    have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ => (1 : ℝ)) p
    simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one] at this
    rw [← hq]; exact this
  set μ' := x ⬝ᵥ S / n with hμ'
  have hμ'0 : 0 < μ' := by
    rw [hμ']; apply div_pos _ hn'
    have j : Fin n := ⟨0, hn⟩
    exact Finset.sum_pos (fun i _ => mul_pos (hx i) (hSpos i)) ⟨j, Finset.mem_univ j⟩
  refine ⟨hSpos, ?_, ?_⟩
  · -- centrality
    have hdev : ∀ j, x j * S j - μ' = (p j - a) / t := by
      intro j; rw [eq_div_iff ht0.ne', hpj j]; linear_combination (-1 : ℝ) * hmu
    have hsq : ∑ j, (x j * S j - μ') ^ 2 = (N ^ 2 - n * a ^ 2) / t ^ 2 := by
      simp only [hdev, div_pow, ← Finset.sum_div]
      congr 1
      have : ∑ j, (p j - a) ^ 2 = ∑ j, p j ^ 2 - 2 * a * ∑ j, p j + n * a ^ 2 := by
        have h := fun j => (show (p j - a) ^ 2 = p j ^ 2 - 2 * a * p j + a ^ 2 by ring)
        rw [Finset.sum_congr rfl (fun j _ => h j), Finset.sum_add_distrib,
          Finset.sum_sub_distrib, ← Finset.mul_sum]
        simp
      rw [this, hq, hsum_p]; ring
    unfold norm2
    rw [Real.sqrt_lt' (mul_pos hη hμ'0), hsq, div_lt_iff₀ (by positivity)]
    have hq2 : N ^ 2 * (n + η ^ 2) < η ^ 2 * n := by
      have h3 : N ^ 2 < (η * Real.sqrt (n / (n + η ^ 2))) ^ 2 := by
        exact pow_lt_pow_left₀ hp2 hN0 two_ne_zero
      rw [mul_pow, Real.sq_sqrt (by positivity)] at h3
      rw [mul_div_assoc', lt_div_iff₀ (by positivity)] at h3
      linarith
    have hid : (η * μ') ^ 2 * t ^ 2 = η ^ 2 * (1 + a) ^ 2 := by
      rw [← hmu]; ring
    rw [hid]
    have hpos : 0 < n + η ^ 2 := by positivity
    have key : (n + η ^ 2) * (η ^ 2 * (1 + a) ^ 2 - (N ^ 2 - n * a ^ 2)) =
        ((n + η ^ 2) * a + η ^ 2) ^ 2 + (η ^ 2 * n - N ^ 2 * (n + η ^ 2)) := by ring
    have : 0 < (n + η ^ 2) * (η ^ 2 * (1 + a) ^ 2 - (N ^ 2 - n * a ^ 2)) := by
      rw [key]; nlinarith [sq_nonneg ((n + η ^ 2) * a + η ^ 2)]
    have := (pos_iff_pos_of_mul_pos this).1 hpos
    linarith
  · -- reduction of mu
    have haN : a * ρ ≤ N := by
      have h1 : (n * a) ^ 2 ≤ n * N ^ 2 := by rw [← hsum_p]; exact hcs
      have h2 : (a * ρ) ^ 2 ≤ N ^ 2 := by
        have : (n * a) ^ 2 = n * (a * ρ) ^ 2 := by rw [mul_pow a, hr2]; ring
        rw [this] at h1; exact le_of_mul_le_mul_left h1 hn'
      exact abs_le_of_sq_le_sq' h2 hN0 |>.2
    have hμ'eq : μ' = (1 + a) / t := by rw [eq_div_iff ht0.ne']; linarith [hmu]
    rw [hμ'eq, ← hgap, ht, div_div_eq_mul_div]
    rw [div_lt_iff₀ hK0, ← hr2]
    -- (1+a) Δ < (1 - η/(2ρ)) (Δ/ρ^2) (ρ^2 + ρ)
    have hρ0 : 0 < ρ := by linarith
    have hK' : K = ρ ^ 2 + ρ := by rw [hK, hr2]
    rw [hK']
    have ha' : a * ρ < 1 - η := lt_of_le_of_lt haN hp1
    have e : (1 - η / (2 * ρ)) * (Δ / ρ ^ 2) * (ρ ^ 2 + ρ) =
        Δ * ((2 * ρ - η) * (ρ + 1)) / (2 * ρ ^ 2) := by field_simp
    rw [e, lt_div_iff₀ (by positivity)]
    -- (1+a) * 2ρ^2 < (2ρ - η)(ρ+1), using a ρ < 1 - η and η(ρ - 1) ≥ 0
    have : (1 + a) * (2 * ρ ^ 2) < (2 * ρ - η) * (ρ + 1) := by
      have h1 : (1 + a) * (2 * ρ ^ 2) = 2 * ρ ^ 2 + 2 * ρ * (a * ρ) := by ring
      have h2 : 2 * ρ * (a * ρ) < 2 * ρ * (1 - η) := mul_lt_mul_of_pos_left ha' (by positivity)
      have h3 := mul_nonneg hη.le (by linarith : (0:ℝ) ≤ ρ - 1)
      rw [h1, show (2 * ρ - η) * (ρ + 1) = 2 * ρ ^ 2 + 2 * ρ * (1 - η) + η * (ρ - 1) by ring]
      linarith
    have h := mul_lt_mul_of_pos_left this hΔ0
    calc _ = Δ * ((1 + a) * (2 * ρ ^ 2)) := by ring
      _ < _ := h

theorem g70ye_amgm {n : ℕ} (hn : 0 < n) (v : Fin n → ℝ) (hv : ∀ j, 0 < v j) :
    n * Real.log n ≤ n * Real.log (∑ j, v j) - ∑ j, Real.log (v j) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hS : 0 < ∑ j, v j := by
    have j : Fin n := ⟨0, hn⟩
    exact Finset.sum_pos (fun i _ => hv i) ⟨j, Finset.mem_univ j⟩
  set μ := (∑ j, v j) / n with hμ
  have hμ0 : 0 < μ := div_pos hS hn'
  have h1 : ∑ j, Real.log (v j / μ) ≤ ∑ j, (v j / μ - 1) :=
    Finset.sum_le_sum fun j _ => Real.log_le_sub_one_of_pos (div_pos (hv j) hμ0)
  have h2 : ∑ j, (v j / μ - 1) = 0 := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_div, hμ]; simp; field_simp; ring
  have h3 : ∑ j, Real.log (v j / μ) = ∑ j, Real.log (v j) - n * Real.log μ := by
    rw [Finset.sum_congr rfl fun j _ => Real.log_div (hv j).ne' hμ0.ne', Finset.sum_sub_distrib]
    simp
  have h4 : Real.log (∑ j, v j) = Real.log n + Real.log μ := by
    rw [← Real.log_mul hn'.ne' hμ0.ne', hμ]; field_simp
  rw [h4]; nlinarith

theorem g70ye_central {n : ℕ} (hn : 0 < n) (v : Fin n → ℝ) (hv : ∀ j, 0 < v j) (η : ℝ)
    (hη0 : 0 < η) (hη1 : η < 1)
    (hc : Real.sqrt (∑ j, (v j - (∑ i, v i) / n) ^ 2) < η * ((∑ i, v i) / n)) :
    n * Real.log (∑ j, v j) - ∑ j, Real.log (v j) ≤ n * Real.log n + η ^ 2 / (2 * (1 - η)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hS : 0 < ∑ j, v j := by
    have j : Fin n := ⟨0, hn⟩
    exact Finset.sum_pos (fun i _ => hv i) ⟨j, Finset.mem_univ j⟩
  set μ := (∑ j, v j) / n with hμ
  have hμ0 : 0 < μ := div_pos hS hn'
  set d : Fin n → ℝ := fun j => v j / μ - 1 with hd
  have hdsq : ∑ j, d j ^ 2 < η ^ 2 := by
    have e : ∑ j, d j ^ 2 = (∑ j, (v j - μ) ^ 2) / μ ^ 2 := by
      rw [Finset.sum_div]; refine Finset.sum_congr rfl fun j _ => ?_
      simp only [hd]; field_simp
    rw [e, div_lt_iff₀ (by positivity)]
    have h0 : 0 ≤ ∑ j, (v j - μ) ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
    have := Real.sq_sqrt h0
    have hs0 := Real.sqrt_nonneg (∑ j, (v j - μ) ^ 2)
    nlinarith
  have hdj : ∀ j, |d j| ≤ η := by
    intro j
    have h := Finset.single_le_sum (f := fun j => d j ^ 2) (fun i _ => sq_nonneg _)
      (Finset.mem_univ j)
    exact abs_le.2 (abs_le_of_sq_le_sq' (by linarith) hη0.le)
  have hsumd : ∑ j, d j = 0 := by
    simp only [hd]; rw [Finset.sum_sub_distrib, ← Finset.sum_div, hμ]; simp; field_simp; ring
  have hlog : ∑ j, (d j - d j ^ 2 / (2 * (1 - η))) ≤ ∑ j, Real.log (1 + d j) :=
    Finset.sum_le_sum fun j _ => g70ye_log_term (hdj j) hη1
  have hv' : ∀ j, v j = μ * (1 + d j) := fun j => by simp only [hd]; field_simp; ring
  have hpd : ∀ j, 0 < 1 + d j := fun j => by have := (abs_le.1 (hdj j)).1; linarith
  have hlv : ∑ j, Real.log (v j) = n * Real.log μ + ∑ j, Real.log (1 + d j) := by
    have : ∀ j, Real.log (v j) = Real.log μ + Real.log (1 + d j) := fun j => by
      rw [hv' j, Real.log_mul hμ0.ne' (hpd j).ne']
    rw [Finset.sum_congr rfl fun j _ => this j, Finset.sum_add_distrib]; simp
  have h4 : Real.log (∑ j, v j) = Real.log n + Real.log μ := by
    rw [← Real.log_mul hn'.ne' hμ0.ne', hμ]; field_simp
  rw [Finset.sum_sub_distrib, hsumd, ← Finset.sum_div] at hlog
  have : (∑ j, d j ^ 2) / (2 * (1 - η)) ≤ η ^ 2 / (2 * (1 - η)) :=
    div_le_div_of_nonneg_right hdsq.le (by linarith)
  rw [h4, hlv]; nlinarith


/-- Theorem 4.9 (Ye 1997, p. 124). There is a constant `δ > 1/20` such that the following holds
for every standard-form LP satisfying the standing assumptions (p. 63) and every
`(xᵏ, yᵏ, sᵏ) ∈ F̊`. Let `ρ = √n`, `zᵏ = bᵀyᵏ`, let `xᵏ⁺¹` be given by (4.10) with the step
length `α = .3` that the proof fixes (p. 125), and let `yᵏ⁺¹ = y(zᵏ)` (4.13) and
`sᵏ⁺¹ = s(zᵏ)` (4.12). Then either `ψ_{n+ρ}(xᵏ⁺¹, sᵏ) ≤ ψ_{n+ρ}(xᵏ, sᵏ) − δ` or
`ψ_{n+ρ}(xᵏ, sᵏ⁺¹) ≤ ψ_{n+ρ}(xᵏ, sᵏ) − δ`. -/
theorem solution :
    ∃ δ : ℝ, 1 / 20 < δ ∧
      ∀ (m n : ℕ), 0 < n → ∀ (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ),
        StandingAssumptions A b c →
        ∀ (x : Fin n → ℝ) (y : Fin m → ℝ) (s : Fin n → ℝ), IsInteriorFeasible A b c x y s →
          pdPotential (Real.sqrt n) (primalStep A c (Real.sqrt n) (3 / 10) x (b ⬝ᵥ y)) s ≤
              pdPotential (Real.sqrt n) x s - δ ∨
            pdPotential (Real.sqrt n) x (sOf A b c (Real.sqrt n) x (b ⬝ᵥ y)) ≤
              pdPotential (Real.sqrt n) x s - δ := by
  refine ⟨515 / 10000, by norm_num, ?_⟩
  intro m n hn A b c hA x y s hF
  obtain ⟨hAx, hx, hAy, hs⟩ := hF
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set ρ := Real.sqrt n with hρ
  have hρ0 : 0 < ρ := Real.sqrt_pos.2 hn'
  set η : ℝ := 21 / 50 with hη
  have hxs : 0 < x ⬝ᵥ s := by
    have j : Fin n := ⟨0, hn⟩
    exact Finset.sum_pos (fun i _ => mul_pos (hx i) (hs i)) ⟨j, Finset.mem_univ j⟩
  by_cases hsmall : norm2 (pVec A c ρ x (b ⬝ᵥ y)) < min (η * Real.sqrt (n / (n + η ^ 2))) (1 - η)
  · right
    obtain ⟨h1, h2, h3⟩ := g70ye_smallp hn A b c hA x y s ⟨hAx, hx, hAy, hs⟩ η hsmall
    set s' := sOf A b c ρ x (b ⬝ᵥ y)
    have hv' : ∀ j, 0 < x j * s' j := fun j => mul_pos (hx j) (h1 j)
    have hv : ∀ j, 0 < x j * s j := fun j => mul_pos (hx j) (hs j)
    have hc := g70ye_central hn (fun j => x j * s' j) hv' η (by norm_num) (by norm_num) h2
    have ham := g70ye_amgm hn (fun j => x j * s j) hv
    have hxs' : 0 < x ⬝ᵥ s' := by
      have j : Fin n := ⟨0, hn⟩
      exact Finset.sum_pos (fun i _ => hv' i) ⟨j, Finset.mem_univ j⟩
    have hratio : x ⬝ᵥ s' / (x ⬝ᵥ s) < 1 - η / (2 * ρ) := by
      rw [div_lt_iff₀ hxs]
      have := h3; rw [div_lt_iff₀ hn'] at this
      have e : (1 - η / (2 * ρ)) * (x ⬝ᵥ s / n) * n = (1 - η / (2 * ρ)) * (x ⬝ᵥ s) := by
        field_simp
      linarith
    have hlogr : Real.log (x ⬝ᵥ s') - Real.log (x ⬝ᵥ s) ≤ -(η / (2 * ρ)) := by
      rw [← Real.log_div hxs'.ne' hxs.ne']
      have := Real.log_le_sub_one_of_pos (div_pos hxs' hxs)
      linarith
    have hρl := mul_le_mul_of_nonneg_left hlogr hρ0.le
    have e1 : ρ * -(η / (2 * ρ)) = -(η / 2) := by field_simp
    rw [e1] at hρl
    unfold pdPotential
    have hd1 : x ⬝ᵥ s' = ∑ j, x j * s' j := rfl
    have hd2 : x ⬝ᵥ s = ∑ j, x j * s j := rfl
    rw [hd1, hd2] at hρl
    rw [hd1, hd2]
    norm_num [hη] at hc ⊢
    nlinarith
  · left
    push_neg at hsmall
    have hT : 386 / 1000 ≤ min (η * Real.sqrt (n / (n + η ^ 2))) (1 - η) := by
      refine le_min ?_ (by norm_num [hη])
      rw [← div_le_iff₀' (by norm_num [hη] : (0:ℝ) < η)]
      apply Real.le_sqrt_of_sq_le
      rw [le_div_iff₀ (by positivity)]
      norm_num [hη]; nlinarith
    obtain ⟨hpos, hAxp, hbound⟩ := g70ye_pstep hn A b c hA x y s ⟨hAx, hx, hAy, hs⟩ (3 / 10)
      (by norm_num) (by norm_num)
    set xp := primalStep A c ρ (3 / 10) x (b ⬝ᵥ y)
    have hg1 := g70ye_gap A b c xp y s hAxp hAy
    have hg2 := g70ye_gap A b c x y s hAx hAy
    have hdiff : pdPotential ρ xp s - pdPotential ρ x s =
        primalPotential ρ c xp (b ⬝ᵥ y) - primalPotential ρ c x (b ⬝ᵥ y) := by
      unfold pdPotential primalPotential
      rw [show c ⬝ᵥ xp - b ⬝ᵥ y = xp ⬝ᵥ s by linarith,
        show c ⬝ᵥ x - b ⬝ᵥ y = x ⬝ᵥ s by linarith]
      rw [Finset.sum_congr rfl fun j _ => Real.log_mul (hpos j).ne' (hs j).ne',
        Finset.sum_congr rfl fun j _ => Real.log_mul (hx j).ne' (hs j).ne',
        Finset.sum_add_distrib, Finset.sum_add_distrib]
      ring
    have := hsmall.trans' hT
    norm_num at hbound
    nlinarith



