-- Prove2me | solution 1 for WrightPDIPM.Infeasible.theorem_6_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T21:37:02.090441+00:00
-- url     : https://prove2.me/submissions/4b3e6e5c-2892-4ec8-b430-290978c89730

import Mathlib
import Definitions.Def_WrightPDIPM_Infeasible_IPF
open WrightPDIPM.Infeasible

open Filter


section g71w_lib
open Matrix
variable {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ} {c : Fin n → ℝ}
  {γ β σmin σmax : ℝ}
  {x : ℕ → Fin n → ℝ} {lam : ℕ → Fin m → ℝ} {s : ℕ → Fin n → ℝ} {σ α : ℕ → ℝ}
  {dx : ℕ → Fin n → ℝ} {dlam : ℕ → Fin m → ℝ} {ds : ℕ → Fin n → ℝ}

theorem g71w_alpha_mem (hrun : IsIPFIterates A b c γ β σmin σmax x lam s σ α dx dlam ds) (k : ℕ) :
    α k ∈ Set.Icc (0:ℝ) 1 ∧
    (x (k+1), lam (k+1), s (k+1)) ∈ NegInfNbhd A b c γ β (x 0) (lam 0) (s 0) ∧
    mu (x (k+1)) (s (k+1)) ≤ (1 - 0.01 * α k) * mu (x k) (s k) := by
  have h := (hrun.alpha_greatest k).1
  rw [hrun.update_x k, hrun.update_lam k, hrun.update_s k]
  exact h

theorem g71w_pos (hrun : IsIPFIterates A b c γ β σmin σmax x lam s σ α dx dlam ds) (k : ℕ) :
    (∀ i, 0 < x k i) ∧ (∀ i, 0 < s k i) := by
  cases k with
  | zero => exact hrun.start_pos
  | succ k =>
    obtain ⟨_, h, _⟩ := g71w_alpha_mem hrun k
    exact ⟨h.2.1, h.2.2.1⟩

theorem g71w_mu_succ_le (hrun : IsIPFIterates A b c γ β σmin σmax x lam s σ α dx dlam ds) (k : ℕ) :
    mu (x (k+1)) (s (k+1)) ≤ mu (x k) (s k) := by
  obtain ⟨⟨h0, _⟩, _, h⟩ := g71w_alpha_mem hrun k
  have hmu : 0 ≤ mu (x k) (s k) := by
    unfold mu; apply div_nonneg _ (Nat.cast_nonneg _)
    exact Finset.sum_nonneg (fun i _ => (mul_pos ((g71w_pos hrun k).1 i) ((g71w_pos hrun k).2 i)).le)
  nlinarith

theorem g71w_mu_le0 (hrun : IsIPFIterates A b c γ β σmin σmax x lam s σ α dx dlam ds) (k : ℕ) :
    mu (x k) (s k) ≤ mu (x 0) (s 0) := by
  induction k with
  | zero => exact le_rfl
  | succ k ih => exact (g71w_mu_succ_le hrun k).trans ih

theorem g71w_nu_mem (hrun : IsIPFIterates A b c γ β σmin σmax x lam s σ α dx dlam ds) (k : ℕ) :
    0 ≤ nu α k ∧ nu α k ≤ 1 := by
  unfold nu
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.prod_range_succ]
    obtain ⟨h0, h1⟩ := (g71w_alpha_mem hrun k).1
    constructor
    · exact mul_nonneg ih.1 (by linarith)
    · nlinarith [ih.1, ih.2]

theorem g71w_nu_succ (k : ℕ) : nu α (k+1) = nu α k * (1 - α k) := by
  unfold nu; rw [Finset.prod_range_succ]

theorem g71w_rb (hrun : IsIPFIterates A b c γ β σmin σmax x lam s σ α dx dlam ds) (k : ℕ) :
    rb A b (x k) = nu α k • rb A b (x 0) := by
  induction k with
  | zero => simp [nu]
  | succ k ih =>
    rw [g71w_nu_succ, hrun.update_x k]
    have h2 := (hrun.step k).2.1
    have : rb A b (x k + α k • dx k) = (1 - α k) • rb A b (x k) := by
      unfold rb at *
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, h2]
      ext i; simp; ring
    rw [this, ih, smul_smul, mul_comm]

theorem g71w_rc (hrun : IsIPFIterates A b c γ β σmin σmax x lam s σ α dx dlam ds) (k : ℕ) :
    rc A c (lam k) (s k) = nu α k • rc A c (lam 0) (s 0) := by
  induction k with
  | zero => simp [nu]
  | succ k ih =>
    rw [g71w_nu_succ, hrun.update_lam k, hrun.update_s k]
    have h1 := (hrun.step k).1
    have : rc A c (lam k + α k • dlam k) (s k + α k • ds k) = (1 - α k) • rc A c (lam k) (s k) := by
      have h1' : ∀ i, (Aᵀ *ᵥ dlam k) i + ds k i = -(rc A c (lam k) (s k)) i := fun i =>
        congrFun h1 i
      unfold rc at *
      ext i
      have := h1' i
      simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Pi.add_apply, Pi.smul_apply, Pi.sub_apply,
        smul_eq_mul, Pi.neg_apply] at this ⊢
      linear_combination α k * this
    rw [this, ih, smul_smul, mul_comm]

/-- the key orthogonality: with `u = ν x0 + (1-ν) xb`, `v = ν s0 + (1-ν) sb`. -/
theorem g71w_orth (hrun : IsIPFIterates A b c γ β σmin σmax x lam s σ α dx dlam ds) (k : ℕ)
    (xb : Fin n → ℝ) (lb : Fin m → ℝ) (sb : Fin n → ℝ) (hxb : A *ᵥ xb = b)
    (hsb : Aᵀ *ᵥ lb + sb = c) :
    (nu α k • x 0 + (1 - nu α k) • xb - x k) ⬝ᵥ (nu α k • s 0 + (1 - nu α k) • sb - s k) = 0 := by
  set ν := nu α k
  have hA : A *ᵥ (ν • x 0 + (1 - ν) • xb - x k) = 0 := by
    have := g71w_rb hrun k
    unfold rb at this
    rw [Matrix.mulVec_sub, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hxb]
    ext i; have := congrFun this i; simp at this ⊢; linarith
  have hS : ν • s 0 + (1 - ν) • sb - s k = Aᵀ *ᵥ (lam k - (ν • lam 0 + (1 - ν) • lb)) := by
    have := g71w_rc hrun k
    unfold rc at this
    ext i
    have h1 := congrFun this i
    have h2 := congrFun hsb i
    simp only [Matrix.mulVec_sub, Matrix.mulVec_add, Matrix.mulVec_smul, Pi.add_apply,
      Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at h1 h2 ⊢
    linear_combination -h1 + (1 - ν) * h2
  rw [hS, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, hA, zero_dotProduct]

end g71w_lib

section g71w_mn
open Matrix
variable {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ} {c : Fin n → ℝ}
  {γ β σmin σmax : ℝ}
  {x : ℕ → Fin n → ℝ} {lam : ℕ → Fin m → ℝ} {s : ℕ → Fin n → ℝ} {σ α : ℕ → ℝ}
  {dx : ℕ → Fin n → ℝ} {dlam : ℕ → Fin m → ℝ} {ds : ℕ → Fin n → ℝ}

theorem g71w_main (hrun : IsIPFIterates A b c γ β σmin σmax x lam s σ α dx dlam ds)
    (p : (Fin n → ℝ) × (Fin m → ℝ) × (Fin n → ℝ)) (hp : p ∈ Omega A b c) (k : ℕ) :
    nu α k * ∑ i, (s 0 i * x k i + x 0 i * s k i) ≤
      nu α k * ∑ i, (x 0 i * s 0 i + x 0 i * p.2.2 i + p.1 i * s 0 i) + ∑ i, x k i * s k i := by
  obtain ⟨hsb, hxb, hcomp, hxp, hsp⟩ := hp
  have horth := g71w_orth hrun k p.1 p.2.1 p.2.2 hxb hsb
  obtain ⟨hν0, hν1⟩ := g71w_nu_mem hrun k
  have hxk := (g71w_pos hrun k).1
  have hsk := (g71w_pos hrun k).2
  have hx0 := hrun.start_pos.1
  have hs0 := hrun.start_pos.2
  set ν := nu α k
  have hsum : ∑ i, ((ν * x 0 i + (1 - ν) * p.1 i - x k i) * (ν * s 0 i + (1 - ν) * p.2.2 i - s k i)) = 0 := by
    rw [← horth]; unfold dotProduct; rfl
  have h1 : ∀ i, ν * (s 0 i * x k i + x 0 i * s k i) ≤
      ν * (x 0 i * s 0 i + x 0 i * p.2.2 i + p.1 i * s 0 i) + x k i * s k i
      - ((ν * x 0 i + (1 - ν) * p.1 i - x k i) * (ν * s 0 i + (1 - ν) * p.2.2 i - s k i)) := by
    intro i
    have e : (ν * x 0 i + (1 - ν) * p.1 i - x k i) * (ν * s 0 i + (1 - ν) * p.2.2 i - s k i)
        = ν^2 * (x 0 i * s 0 i) + ν * (1 - ν) * (x 0 i * p.2.2 i + p.1 i * s 0 i)
          + (1-ν)^2 * (p.1 i * p.2.2 i)
          - ν * (s 0 i * x k i + x 0 i * s k i) - (1 - ν) * (p.1 i * s k i + p.2.2 i * x k i)
          + x k i * s k i := by ring
    rw [e, hcomp i]
    have a1 : 0 ≤ x 0 i * s 0 i := (mul_pos (hx0 i) (hs0 i)).le
    have a2 : 0 ≤ x 0 i * p.2.2 i + p.1 i * s 0 i :=
      add_nonneg (mul_nonneg (hx0 i).le (hsp i)) (mul_nonneg (hxp i) (hs0 i).le)
    have a3 : 0 ≤ p.1 i * s k i + p.2.2 i * x k i :=
      add_nonneg (mul_nonneg (hxp i) (hsk i).le) (mul_nonneg (hsp i) (hxk i).le)
    have b1 : ν ^ 2 ≤ ν := by nlinarith
    have b2 : ν * (1 - ν) ≤ ν := by nlinarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hν1) a3, mul_le_mul_of_nonneg_right b1 a1,
      mul_le_mul_of_nonneg_right b2 a2]
  have := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => h1 i)
  rw [Finset.sum_sub_distrib, hsum, sub_zero, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum] at this
  exact this

theorem g71w_resNorm (hrun : IsIPFIterates A b c γ β σmin σmax x lam s σ α dx dlam ds) (k : ℕ) :
    resNorm A b c (x k) (lam k) (s k) = nu α k * resNorm A b c (x 0) (lam 0) (s 0) := by
  unfold resNorm
  rw [g71w_rb hrun k, g71w_rc hrun k]
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow]
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← mul_add, Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq (g71w_nu_mem hrun k).1]

theorem g71w_res0_pos (hinf : (rb A b (x 0), rc A c (lam 0) (s 0)) ≠ (0, 0)) :
    0 < resNorm A b c (x 0) (lam 0) (s 0) := by
  unfold resNorm
  apply Real.sqrt_pos.mpr
  by_contra hc
  push_neg at hc
  have h1 : 0 ≤ ∑ i, rb A b (x 0) i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have h2 : 0 ≤ ∑ j, rc A c (lam 0) (s 0) j ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have e1 := (Finset.sum_eq_zero_iff_of_nonneg (fun i (_ : i ∈ Finset.univ) => sq_nonneg (rb A b (x 0) i))).mp (by linarith)
  have e2 := (Finset.sum_eq_zero_iff_of_nonneg (fun i (_ : i ∈ Finset.univ) => sq_nonneg (rc A c (lam 0) (s 0) i))).mp (by linarith)
  apply hinf
  ext i
  · simpa using e1 i (Finset.mem_univ _)
  · simpa using e2 i (Finset.mem_univ _)

theorem g71w_mu_pos (hrun : IsIPFIterates A b c γ β σmin σmax x lam s σ α dx dlam ds) (hn : 0 < n)
    (k : ℕ) : 0 < mu (x k) (s k) := by
  unfold mu
  apply div_pos _ (by exact_mod_cast hn)
  exact Finset.sum_pos (fun i _ => mul_pos ((g71w_pos hrun k).1 i) ((g71w_pos hrun k).2 i))
    ⟨⟨0, hn⟩, Finset.mem_univ _⟩

theorem g71w_nu_mu (hrun : IsIPFIterates A b c γ β σmin σmax x lam s σ α dx dlam ds)
    (hβ : 1 ≤ β) (hn : 0 < n)
    (hinf : (rb A b (x 0), rc A c (lam 0) (s 0)) ≠ (0, 0)) (k : ℕ) :
    nu α k * mu (x 0) (s 0) ≤ β * mu (x k) (s k) := by
  cases k with
  | zero =>
    have := g71w_mu_pos hrun hn 0
    simp [nu]; nlinarith
  | succ k =>
    have h := (g71w_alpha_mem hrun k).2.1.1
    simp only at h
    rw [g71w_resNorm hrun (k+1)] at h
    have hR := g71w_res0_pos hinf
    have hm0 := g71w_mu_pos hrun hn 0
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hm0] at h
    have : resNorm A b c (x 0) (lam 0) (s 0) * (nu α (k+1) * mu (x 0) (s 0)) ≤
        resNorm A b c (x 0) (lam 0) (s 0) * (β * mu (x (k+1)) (s (k+1))) := by linarith
    exact le_of_mul_le_mul_left this hR

end g71w_mn

section g71w_st
open Matrix
variable {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ} {c : Fin n → ℝ}
  {γ β σmin σmax : ℝ}
  {x : ℕ → Fin n → ℝ} {lam : ℕ → Fin m → ℝ} {s : ℕ → Fin n → ℝ} {σ α : ℕ → ℝ}
  {dx : ℕ → Fin n → ℝ} {dlam : ℕ → Fin m → ℝ} {ds : ℕ → Fin n → ℝ}

theorem g71w_main2 (hrun : IsIPFIterates A b c γ β σmin σmax x lam s σ α dx dlam ds)
    (p : (Fin n → ℝ) × (Fin m → ℝ) × (Fin n → ℝ)) (hp : p ∈ Omega A b c) (k : ℕ) :
    nu α k * ∑ i, (s 0 i * x k i + x 0 i * s k i) ≤
      ∑ i, (nu α k ^ 2 * (x 0 i * s 0 i) + nu α k * (1 - nu α k) * (x 0 i * p.2.2 i + p.1 i * s 0 i))
        + ∑ i, x k i * s k i := by
  obtain ⟨hsb, hxb, hcomp, hxp, hsp⟩ := hp
  have horth := g71w_orth hrun k p.1 p.2.1 p.2.2 hxb hsb
  obtain ⟨hν0, hν1⟩ := g71w_nu_mem hrun k
  have hxk := (g71w_pos hrun k).1
  have hsk := (g71w_pos hrun k).2
  set ν := nu α k
  have hsum : ∑ i, ((ν * x 0 i + (1 - ν) * p.1 i - x k i) * (ν * s 0 i + (1 - ν) * p.2.2 i - s k i)) = 0 := by
    rw [← horth]; unfold dotProduct; rfl
  have h1 : ∀ i, ν * (s 0 i * x k i + x 0 i * s k i) ≤
      (ν ^ 2 * (x 0 i * s 0 i) + ν * (1 - ν) * (x 0 i * p.2.2 i + p.1 i * s 0 i)) + x k i * s k i
      - ((ν * x 0 i + (1 - ν) * p.1 i - x k i) * (ν * s 0 i + (1 - ν) * p.2.2 i - s k i)) := by
    intro i
    have e : (ν * x 0 i + (1 - ν) * p.1 i - x k i) * (ν * s 0 i + (1 - ν) * p.2.2 i - s k i)
        = ν^2 * (x 0 i * s 0 i) + ν * (1 - ν) * (x 0 i * p.2.2 i + p.1 i * s 0 i)
          + (1-ν)^2 * (p.1 i * p.2.2 i)
          - ν * (s 0 i * x k i + x 0 i * s k i) - (1 - ν) * (p.1 i * s k i + p.2.2 i * x k i)
          + x k i * s k i := by ring
    rw [e, hcomp i]
    have a3 : 0 ≤ p.1 i * s k i + p.2.2 i * x k i :=
      add_nonneg (mul_nonneg (hxp i) (hsk i).le) (mul_nonneg (hsp i) (hxk i).le)
    nlinarith [mul_nonneg (sub_nonneg.mpr hν1) a3]
  have := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => h1 i)
  rw [Finset.sum_sub_distrib, hsum, sub_zero, Finset.sum_add_distrib, ← Finset.mul_sum] at this
  exact this

theorem g71w_step_orth (hrun : IsIPFIterates A b c γ β σmin σmax x lam s σ α dx dlam ds) (k : ℕ)
    (xb : Fin n → ℝ) (lb : Fin m → ℝ) (sb : Fin n → ℝ) (hxb : A *ᵥ xb = b)
    (hsb : Aᵀ *ᵥ lb + sb = c) :
    ∑ i, (dx k i + nu α k * (x 0 i - xb i)) * (ds k i + nu α k * (s 0 i - sb i)) = 0 := by
  obtain ⟨h1, h2, _⟩ := hrun.step k
  have hA : A *ᵥ (dx k + nu α k • (x 0 - xb)) = 0 := by
    have := g71w_rb hrun k
    unfold rb at this h2
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_sub, hxb, h2, this]
    ext i; simp
  have hS : ds k + nu α k • (s 0 - sb) = Aᵀ *ᵥ (-(dlam k + nu α k • (lam 0 - lb))) := by
    have := g71w_rc hrun k
    unfold rc at this h1
    ext i
    have e1 := congrFun this i
    have e2 := congrFun hsb i
    have e3 := congrFun h1 i
    simp only [Matrix.mulVec_neg, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_sub, Pi.add_apply,
      Pi.smul_apply, Pi.sub_apply, Pi.neg_apply, smul_eq_mul] at e1 e2 e3 ⊢
    linear_combination e3 - e1 - nu α k * e2
  have : (dx k + nu α k • (x 0 - xb)) ⬝ᵥ (ds k + nu α k • (s 0 - sb)) = 0 := by
    rw [hS, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, hA, zero_dotProduct]
  rw [← this]; unfold dotProduct; rfl

theorem g71w_cen (hrun : IsIPFIterates A b c γ β σmin σmax x lam s σ α dx dlam ds) (k : ℕ) :
    ∀ i, γ * mu (x (k+1)) (s (k+1)) ≤ x (k+1) i * s (k+1) i :=
  (g71w_alpha_mem hrun k).2.1.2.2.2

end g71w_st

section g71w_cr
open Matrix

theorem g71w_n2_eq {n : ℕ} (w : Fin n → ℝ) :
    norm2 w = ‖(WithLp.toLp 2 w : EuclideanSpace ℝ (Fin n))‖ := by
  rw [EuclideanSpace.norm_eq]; simp [norm2, Real.norm_eq_abs, sq_abs]

theorem g71w_n2_add {n : ℕ} (u v : Fin n → ℝ) : norm2 (u + v) ≤ norm2 u + norm2 v := by
  rw [g71w_n2_eq, g71w_n2_eq, g71w_n2_eq, WithLp.toLp_add]; exact norm_add_le _ _

theorem g71w_n2_le {n : ℕ} (u : Fin n → ℝ) (C : ℝ) (hC : 0 ≤ C) (h : ∑ i, u i ^ 2 ≤ C ^ 2) :
    norm2 u ≤ C := by
  unfold norm2; rw [← Real.sqrt_sq hC]; exact Real.sqrt_le_sqrt h

theorem g71w_n2_mono {n : ℕ} (u v : Fin n → ℝ) (h : ∑ i, u i ^ 2 ≤ ∑ i, v i ^ 2) :
    norm2 u ≤ norm2 v := Real.sqrt_le_sqrt h

theorem g71w_core {n : ℕ} (x s dx ds z z' : Fin n → ℝ) (ν σ μ γ Z : ℝ)
    (hx : ∀ i, 0 < x i) (hs : ∀ i, 0 < s i) (hμ : 0 < μ) (hγ : 0 < γ) (hν : 0 ≤ ν)
    (hσ : 0 ≤ σ) (hZ : 0 ≤ Z)
    (hcen : ∀ i, γ * μ ≤ x i * s i) (hsum : ∑ i, x i * s i = n * μ)
    (hstep : ∀ i, s i * dx i + x i * ds i = -(x i * s i) + σ * μ)
    (horth : ∑ i, (dx i + ν * z i) * (ds i + ν * z' i) = 0)
    (hz : ∀ i, |z i| ≤ Z) (hz' : ∀ i, |z' i| ≤ Z) :
    norm2 (scaledDx x s dx) ≤ Real.sqrt (n * (1 + σ ^ 2 / γ) * μ) +
        (2 * (ν * Z * ∑ i, s i) + ν * Z * ∑ i, x i) / Real.sqrt (γ * μ) ∧
    norm2 (scaledDs x s ds) ≤ Real.sqrt (n * (1 + σ ^ 2 / γ) * μ) +
        (ν * Z * ∑ i, s i + 2 * (ν * Z * ∑ i, x i)) / Real.sqrt (γ * μ) := by
  set al : Fin n → ℝ := fun i => Real.sqrt (s i / x i) with hal
  set be : Fin n → ℝ := fun i => Real.sqrt (x i / s i) with hbe
  have hal2 : ∀ i, al i ^ 2 * x i = s i := fun i => by
    simp only [hal]; rw [Real.sq_sqrt (div_pos (hs i) (hx i)).le]; field_simp [(hx i).ne']
  have hbe2 : ∀ i, be i ^ 2 * s i = x i := fun i => by
    simp only [hbe]; rw [Real.sq_sqrt (div_pos (hx i) (hs i)).le]; field_simp [(hs i).ne']
  have hab : ∀ i, al i * be i = 1 := fun i => by
    simp only [hal, hbe]; rw [← Real.sqrt_mul (div_pos (hs i) (hx i)).le]
    rw [div_mul_div_comm, mul_comm (s i), div_self (mul_pos (hx i) (hs i)).ne', Real.sqrt_one]
  have hgm : 0 < γ * μ := mul_pos hγ hμ
  have hsq : 0 < Real.sqrt (γ * μ) := Real.sqrt_pos.mpr hgm
  have hsq2 : Real.sqrt (γ * μ) ^ 2 = γ * μ := Real.sq_sqrt hgm.le
  set P : Fin n → ℝ := fun i => al i * (ν * z i) with hP
  set Q : Fin n → ℝ := fun i => be i * (ν * z' i) with hQ
  set a : Fin n → ℝ := scaledDx x s dx + P with ha
  set b : Fin n → ℝ := scaledDs x s ds + Q with hb
  set r : Fin n → ℝ := scaledDx x s dx + scaledDs x s ds with hr
  have hab0 : ∑ i, a i * b i = 0 := by
    rw [← horth]; refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [ha, hb, Pi.add_apply, scaledDx, scaledDs, hP, hQ]
    have := hab i; simp only [hal, hbe] at this
    linear_combination ((dx i + ν * z i) * (ds i + ν * z' i)) * this
  have hsum_ab : a + b = r + P + Q := by
    funext i; simp only [ha, hb, hr, Pi.add_apply]; ring
  have hna : norm2 a ≤ norm2 (a + b) := by
    apply g71w_n2_mono
    have : ∑ i, (a + b) i ^ 2 = ∑ i, a i ^ 2 + ∑ i, b i ^ 2 + 2 * ∑ i, a i * b i := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_); simp only [Pi.add_apply]; ring
    rw [this, hab0]
    have : 0 ≤ ∑ i, b i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
    linarith
  have hnb : norm2 b ≤ norm2 (a + b) := by
    apply g71w_n2_mono
    have : ∑ i, (a + b) i ^ 2 = ∑ i, a i ^ 2 + ∑ i, b i ^ 2 + 2 * ∑ i, a i * b i := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_); simp only [Pi.add_apply]; ring
    rw [this, hab0]
    have : 0 ≤ ∑ i, a i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
    linarith
  have hnr : norm2 r ≤ Real.sqrt (n * (1 + σ ^ 2 / γ) * μ) := by
    unfold norm2; apply Real.sqrt_le_sqrt
    have hpt : ∀ i, r i ^ 2 ≤ x i * s i + σ ^ 2 / γ * μ := by
      intro i
      have hxs := mul_pos (hx i) (hs i)
      have e : r i ^ 2 * (x i * s i) = (-(x i * s i) + σ * μ) ^ 2 := by
        rw [← hstep i]
        simp only [hr, Pi.add_apply, scaledDx, scaledDs]
        have h1 := hal2 i; have h2 := hbe2 i; have h3 := hab i
        simp only [hal, hbe] at h1 h2 h3
        linear_combination (dx i ^ 2 * s i) * h1 + (2 * dx i * ds i * x i * s i) * h3 +
          (ds i ^ 2 * x i) * h2
      have e2 : (-(x i * s i) + σ * μ) ^ 2 ≤ (x i * s i) * (x i * s i + σ ^ 2 / γ * μ) := by
        have : σ ^ 2 * μ ^ 2 ≤ (x i * s i) * (σ ^ 2 / γ * μ) := by
          rw [div_mul_eq_mul_div, mul_div_assoc']
          rw [le_div_iff₀ hγ]
          have := hcen i
          nlinarith [mul_nonneg (sq_nonneg σ) hμ.le]
        nlinarith [mul_nonneg (mul_nonneg hσ hμ.le) hxs.le]
      have : r i ^ 2 * (x i * s i) ≤ (x i + 0) * s i * (x i * s i + σ ^ 2 / γ * μ) := by
        rw [e]; simpa using e2
      simp only [add_zero] at this
      nlinarith
    calc ∑ i, r i ^ 2 ≤ ∑ i, (x i * s i + σ ^ 2 / γ * μ) := Finset.sum_le_sum (fun i _ => hpt i)
      _ = n * (1 + σ ^ 2 / γ) * μ := by
        rw [Finset.sum_add_distrib, hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]; ring
  have hsS : 0 ≤ ∑ i, s i := Finset.sum_nonneg (fun i _ => (hs i).le)
  have hsX : 0 ≤ ∑ i, x i := Finset.sum_nonneg (fun i _ => (hx i).le)
  have hnP : norm2 P ≤ (ν * Z * ∑ i, s i) / Real.sqrt (γ * μ) := by
    apply g71w_n2_le _ _ (by positivity)
    rw [div_pow, hsq2, le_div_iff₀ hgm, Finset.sum_mul]
    have hpt : ∀ i, P i ^ 2 * (γ * μ) ≤ ν ^ 2 * Z ^ 2 * s i ^ 2 := by
      intro i
      simp only [hP]
      have h1 := hal2 i
      have hz2 : z i ^ 2 ≤ Z ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hz i) 2
      have hc := hcen i
      have : (al i * (ν * z i)) ^ 2 * (γ * μ) ≤ (al i * (ν * z i)) ^ 2 * (x i * s i) :=
        mul_le_mul_of_nonneg_left hc (sq_nonneg _)
      have e : (al i * (ν * z i)) ^ 2 * (x i * s i) = ν ^ 2 * z i ^ 2 * s i ^ 2 := by
        linear_combination (ν ^ 2 * z i ^ 2 * s i) * h1
      rw [e] at this
      nlinarith [mul_le_mul_of_nonneg_left hz2 (mul_nonneg (sq_nonneg ν) (sq_nonneg (s i)))]
    calc ∑ i, P i ^ 2 * (γ * μ) ≤ ∑ i, ν ^ 2 * Z ^ 2 * s i ^ 2 := Finset.sum_le_sum (fun i _ => hpt i)
      _ = ν ^ 2 * Z ^ 2 * ∑ i, s i ^ 2 := by rw [Finset.mul_sum]
      _ ≤ ν ^ 2 * Z ^ 2 * (∑ i, s i) ^ 2 :=
          mul_le_mul_of_nonneg_left (Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => (hs i).le))
            (by positivity)
      _ = (ν * Z * ∑ i, s i) ^ 2 := by ring
  have hnQ : norm2 Q ≤ (ν * Z * ∑ i, x i) / Real.sqrt (γ * μ) := by
    apply g71w_n2_le _ _ (by positivity)
    rw [div_pow, hsq2, le_div_iff₀ hgm, Finset.sum_mul]
    have hpt : ∀ i, Q i ^ 2 * (γ * μ) ≤ ν ^ 2 * Z ^ 2 * x i ^ 2 := by
      intro i
      simp only [hQ]
      have h1 := hbe2 i
      have hz2 : z' i ^ 2 ≤ Z ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hz' i) 2
      have hc := hcen i
      have : (be i * (ν * z' i)) ^ 2 * (γ * μ) ≤ (be i * (ν * z' i)) ^ 2 * (x i * s i) :=
        mul_le_mul_of_nonneg_left hc (sq_nonneg _)
      have e : (be i * (ν * z' i)) ^ 2 * (x i * s i) = ν ^ 2 * z' i ^ 2 * x i ^ 2 := by
        linear_combination (ν ^ 2 * z' i ^ 2 * x i) * h1
      rw [e] at this
      nlinarith [mul_le_mul_of_nonneg_left hz2 (mul_nonneg (sq_nonneg ν) (sq_nonneg (x i)))]
    calc ∑ i, Q i ^ 2 * (γ * μ) ≤ ∑ i, ν ^ 2 * Z ^ 2 * x i ^ 2 := Finset.sum_le_sum (fun i _ => hpt i)
      _ = ν ^ 2 * Z ^ 2 * ∑ i, x i ^ 2 := by rw [Finset.mul_sum]
      _ ≤ ν ^ 2 * Z ^ 2 * (∑ i, x i) ^ 2 :=
          mul_le_mul_of_nonneg_left (Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => (hx i).le))
            (by positivity)
      _ = (ν * Z * ∑ i, x i) ^ 2 := by ring
  have hneg : ∀ w : Fin n → ℝ, norm2 (-w) = norm2 w := fun w => by simp [norm2]
  have hrPQ : norm2 (r + P + Q) ≤ norm2 r + norm2 P + norm2 Q :=
    (g71w_n2_add _ _).trans (by linarith [g71w_n2_add r P])
  have hdx : norm2 (scaledDx x s dx) ≤ norm2 a + norm2 P := by
    have : scaledDx x s dx = a + -P := by simp [ha]
    rw [this]; exact (g71w_n2_add _ _).trans (by rw [hneg])
  have hds : norm2 (scaledDs x s ds) ≤ norm2 b + norm2 Q := by
    have : scaledDs x s ds = b + -Q := by simp [hb]
    rw [this]; exact (g71w_n2_add _ _).trans (by rw [hneg])
  rw [hsum_ab] at hna hnb
  have e1 : (2 * (ν * Z * ∑ i, s i) + ν * Z * ∑ i, x i) / Real.sqrt (γ * μ) =
      2 * ((ν * Z * ∑ i, s i) / Real.sqrt (γ * μ)) + (ν * Z * ∑ i, x i) / Real.sqrt (γ * μ) := by ring
  have e2 : (ν * Z * ∑ i, s i + 2 * (ν * Z * ∑ i, x i)) / Real.sqrt (γ * μ) =
      (ν * Z * ∑ i, s i) / Real.sqrt (γ * μ) + 2 * ((ν * Z * ∑ i, x i) / Real.sqrt (γ * μ)) := by ring
  rw [e1, e2]
  constructor <;> linarith

end g71w_cr

section g71w_l63
open Matrix
theorem g71w_63 {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ} {c : Fin n → ℝ}
  {γ β σmin σmax : ℝ}
  {x : ℕ → Fin n → ℝ} {lam : ℕ → Fin m → ℝ} {s : ℕ → Fin n → ℝ} {σ α : ℕ → ℝ}
  {dx : ℕ → Fin n → ℝ} {dlam : ℕ → Fin m → ℝ} {ds : ℕ → Fin n → ℝ}
    (hrun : IsIPFIterates A b c γ β σmin σmax x lam s σ α dx dlam ds) (hβ : 1 ≤ β) (hn : 0 < n)
    (hinf : (rb A b (x 0), rc A c (lam 0) (s 0)) ≠ (0, 0))
    (hΩ : (Omega A b c).Nonempty) :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ k, nu α k * norm1xs (x k) (s k) ≤ C₁ * mu (x k) (s k) := by
  obtain ⟨p, hp⟩ := hΩ
  have hx0 := hrun.start_pos.1
  have hs0 := hrun.start_pos.2
  have ⟨_, _, _, hxp, hsp⟩ := hp
  set K1 : ℝ := ∑ i, (x 0 i * s 0 i + x 0 i * p.2.2 i + p.1 i * s 0 i) with hK1
  set D : ℝ := ∑ j, (1 / s 0 j + 1 / x 0 j) with hD
  have hK1n : 0 ≤ K1 := Finset.sum_nonneg (fun i _ => by
    have := hx0 i; have := hs0 i; have := hxp i; have := hsp i; positivity)
  have hDn : 0 ≤ D := Finset.sum_nonneg (fun i _ => by
    have := hx0 i; have := hs0 i; positivity)
  have hm0 := g71w_mu_pos hrun hn 0
  have hnr : (0:ℝ) < n := by exact_mod_cast hn
  refine ⟨D * (β * K1 / mu (x 0) (s 0) + n) + 1, by positivity, fun k => ?_⟩
  have hm := g71w_main hrun p hp k
  have hnm := g71w_nu_mu hrun hβ hn hinf k
  obtain ⟨hν0, _⟩ := g71w_nu_mem hrun k
  have hmu := g71w_mu_pos hrun hn k
  have hxk := (g71w_pos hrun k).1
  have hsk := (g71w_pos hrun k).2
  set T := ∑ i, (s 0 i * x k i + x 0 i * s k i) with hT
  have hxs : ∑ i, x k i * s k i = n * mu (x k) (s k) := by
    unfold mu; field_simp; rfl
  rw [hxs] at hm
  have hTj : ∀ j, s 0 j * x k j + x 0 j * s k j ≤ T := fun j =>
    Finset.single_le_sum (f := fun i => s 0 i * x k i + x 0 i * s k i)
      (fun i _ => add_nonneg (mul_pos (hs0 i) (hxk i)).le (mul_pos (hx0 i) (hsk i)).le)
      (Finset.mem_univ j)
  have hN : norm1xs (x k) (s k) ≤ T * D := by
    unfold norm1xs
    rw [hD, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun j _ => ?_)
    rw [abs_of_pos (hxk j), abs_of_pos (hsk j)]
    have h1 : x k j ≤ T * (1 / s 0 j) := by
      rw [mul_one_div, le_div_iff₀ (hs0 j)]
      nlinarith [hTj j, mul_pos (hx0 j) (hsk j)]
    have h2 : s k j ≤ T * (1 / x 0 j) := by
      rw [mul_one_div, le_div_iff₀ (hx0 j)]
      nlinarith [hTj j, mul_pos (hs0 j) (hxk j)]
    linarith
  have hνK : nu α k * K1 ≤ β * K1 / mu (x 0) (s 0) * mu (x k) (s k) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hm0]
    nlinarith
  have hfin : nu α k * norm1xs (x k) (s k) ≤ D * (nu α k * T) := by
    nlinarith [mul_le_mul_of_nonneg_left hN hν0]
  have : nu α k * T ≤ (β * K1 / mu (x 0) (s 0) + n) * mu (x k) (s k) := by
    nlinarith
  have : D * (nu α k * T) ≤ D * ((β * K1 / mu (x 0) (s 0) + n) * mu (x k) (s k)) :=
    mul_le_mul_of_nonneg_left this hDn
  nlinarith
end g71w_l63

set_option maxHeartbeats 1000000 in
/-- Lemma 6.5 (p. 115): along Algorithm IPF, with `Ω ≠ ∅` and an infeasible start, there is a
positive constant `C₂` (independent of `k`) with `‖(Dᵏ)⁻¹Δxᵏ‖ ≤ C₂ μ_k^{1/2}` and
`‖DᵏΔsᵏ‖ ≤ C₂ μ_k^{1/2}` for all `k ≥ 0`, where `Dᵏ = (Xᵏ)^{1/2}(Sᵏ)^{-1/2}`. -/
theorem g72wy_l65 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (γ β σmin σmax : ℝ) (hγ : 0 < γ ∧ γ < 1) (hβ : 1 ≤ β)
    (hσ : 0 < σmin ∧ σmin < σmax ∧ σmax ≤ 0.5)
    (hn : 0 < n)
    (x : ℕ → Fin n → ℝ) (lam : ℕ → Fin m → ℝ) (s : ℕ → Fin n → ℝ) (σ α : ℕ → ℝ)
    (dx : ℕ → Fin n → ℝ) (dlam : ℕ → Fin m → ℝ) (ds : ℕ → Fin n → ℝ)
    (hrun : IsIPFIterates A b c γ β σmin σmax x lam s σ α dx dlam ds)
    (hinf : (rb A b (x 0), rc A c (lam 0) (s 0)) ≠ (0, 0))
    (hΩ : (Omega A b c).Nonempty) :
    ∃ C₂ : ℝ, 0 < C₂ ∧ ∀ k,
      norm2 (scaledDx (x k) (s k) (dx k)) ≤ C₂ * Real.sqrt (mu (x k) (s k)) ∧
      norm2 (scaledDs (x k) (s k) (ds k)) ≤ C₂ * Real.sqrt (mu (x k) (s k)) := by
  obtain ⟨C₁, hC₁, hC⟩ := g71w_63 hrun hβ hn hinf hΩ
  obtain ⟨p, hp⟩ := hΩ
  have ⟨hsb, hxb, _, hxp, hsp⟩ := hp
  have hnr : (0:ℝ) < n := by exact_mod_cast hn
  set Z : ℝ := ∑ i, (|x 0 i - p.1 i| + |s 0 i - p.2.2 i|) with hZ
  have hZi : ∀ i, |x 0 i - p.1 i| ≤ Z ∧ |s 0 i - p.2.2 i| ≤ Z := fun i => by
    have := Finset.single_le_sum (f := fun i => |x 0 i - p.1 i| + |s 0 i - p.2.2 i|)
      (fun j _ => add_nonneg (abs_nonneg _) (abs_nonneg _)) (Finset.mem_univ i)
    constructor <;> linarith [abs_nonneg (x 0 i - p.1 i), abs_nonneg (s 0 i - p.2.2 i)]
  have hZ0 : 0 ≤ Z := Finset.sum_nonneg (fun j _ => add_nonneg (abs_nonneg _) (abs_nonneg _))
  set g := Real.sqrt γ with hg
  have hg0 : 0 < g := Real.sqrt_pos.mpr hγ.1
  set K : ℝ := Real.sqrt (n * (1 + 1 / γ)) + 2 * Z * C₁ / g with hK
  have hK0 : 0 ≤ K := by positivity
  have hm0 := g71w_mu_pos hrun hn 0
  set N0 : ℝ := norm2 (scaledDx (x 0) (s 0) (dx 0)) + norm2 (scaledDs (x 0) (s 0) (ds 0)) with hN0
  have hN00 : 0 ≤ N0 := by
    simp only [hN0, norm2]; positivity
  refine ⟨K + N0 / Real.sqrt (mu (x 0) (s 0)) + 1, by positivity, fun k => ?_⟩
  have hmu := g71w_mu_pos hrun hn k
  set q := Real.sqrt (mu (x k) (s k)) with hq
  have hq0 : 0 < q := Real.sqrt_pos.mpr hmu
  have hqq : q ^ 2 = mu (x k) (s k) := Real.sq_sqrt hmu.le
  have hn2 : ∀ w : Fin n → ℝ, 0 ≤ norm2 w := fun w => Real.sqrt_nonneg _
  suffices H : norm2 (scaledDx (x k) (s k) (dx k)) ≤ (K + N0 / Real.sqrt (mu (x 0) (s 0))) * q ∧
      norm2 (scaledDs (x k) (s k) (ds k)) ≤ (K + N0 / Real.sqrt (mu (x 0) (s 0))) * q by
    constructor <;> nlinarith [H.1, H.2]
  cases k with
  | zero =>
    have e : N0 / Real.sqrt (mu (x 0) (s 0)) * q = N0 := by
      rw [hq]; field_simp
    have : 0 ≤ K * q := by positivity
    rw [add_mul, e]
    constructor <;> [linarith [hn2 (scaledDs (x 0) (s 0) (ds 0))];
      linarith [hn2 (scaledDx (x 0) (s 0) (dx 0))]]
  | succ k =>
  have hextra : 0 ≤ N0 / Real.sqrt (mu (x 0) (s 0)) * q := by positivity
  suffices H : norm2 (scaledDx (x (k+1)) (s (k+1)) (dx (k+1))) ≤ K * q ∧
      norm2 (scaledDs (x (k+1)) (s (k+1)) (ds (k+1))) ≤ K * q by
    rw [add_mul]; constructor <;> linarith [H.1, H.2]
  obtain ⟨hν0, hν1⟩ := g71w_nu_mem hrun (k+1)
  have hsumk : ∑ i, x (k+1) i * s (k+1) i = n * mu (x (k+1)) (s (k+1)) := by
    unfold mu; field_simp; rfl
  have horth := g71w_step_orth hrun (k+1) p.1 p.2.1 p.2.2 hxb hsb
  have hσk := hrun.sigma_mem (k+1)
  have hσ0 : 0 ≤ σ (k+1) := le_trans hσ.1.le hσk.1
  have hσ5 : σ (k+1) ≤ 0.5 := le_trans hσk.2 hσ.2.2
  have hc := g71w_core (x (k+1)) (s (k+1)) (dx (k+1)) (ds (k+1)) (fun i => x 0 i - p.1 i)
    (fun i => s 0 i - p.2.2 i)
    (nu α (k+1)) (σ (k+1)) (mu (x (k+1)) (s (k+1))) γ Z (g71w_pos hrun (k+1)).1
    (g71w_pos hrun (k+1)).2 hmu hγ.1 hν0 hσ0
    hZ0 (g71w_cen hrun k) hsumk (hrun.step (k+1)).2.2 horth (fun i => (hZi i).1) (fun i => (hZi i).2)
  have hgq : Real.sqrt (γ * mu (x (k+1)) (s (k+1))) = g * q := Real.sqrt_mul hγ.1.le _
  rw [hgq] at hc
  have hxk := (g71w_pos hrun (k+1)).1
  have hsk := (g71w_pos hrun (k+1)).2
  have hN : norm1xs (x (k+1)) (s (k+1)) = ∑ i, x (k+1) i + ∑ i, s (k+1) i := by
    unfold norm1xs; congr 1 <;> refine Finset.sum_congr rfl (fun i _ => ?_)
    · exact abs_of_pos (hxk i)
    · exact abs_of_pos (hsk i)
  have hCk := hC (k+1)
  rw [hN] at hCk
  have hsX : 0 ≤ ∑ i, x (k+1) i := Finset.sum_nonneg (fun i _ => (hxk i).le)
  have hsS : 0 ≤ ∑ i, s (k+1) i := Finset.sum_nonneg (fun i _ => (hsk i).le)
  have T1 : Real.sqrt (n * (1 + σ (k+1) ^ 2 / γ) * mu (x (k+1)) (s (k+1))) ≤
      Real.sqrt (n * (1 + 1 / γ)) * q := by
    rw [hq, ← Real.sqrt_mul (mul_nonneg hnr.le (by have := hγ.1; positivity))]
    apply Real.sqrt_le_sqrt
    apply mul_le_mul_of_nonneg_right _ hmu.le
    apply mul_le_mul_of_nonneg_left _ hnr.le
    have : σ (k+1) ^ 2 ≤ 1 := by nlinarith
    have := div_le_div_of_nonneg_right this hγ.1.le
    linarith
  have T2 : ∀ A B : ℝ, 0 ≤ A → 0 ≤ B → A + B ≤ nu α (k+1) * Z * (∑ i, x (k+1) i + ∑ i, s (k+1) i) →
      (2 * A + B) / (g * q) ≤ 2 * Z * C₁ / g * q ∧ (A + 2 * B) / (g * q) ≤ 2 * Z * C₁ / g * q := by
    intro A B hA hB hAB
    have hb : A + B ≤ Z * C₁ * mu (x (k+1)) (s (k+1)) := by
      have := mul_le_mul_of_nonneg_left hCk hZ0
      nlinarith
    have e : 2 * Z * C₁ / g * q = 2 * (Z * C₁ * mu (x (k+1)) (s (k+1))) / (g * q) := by
      rw [← hqq]; field_simp
    rw [e]
    constructor <;> apply div_le_div_of_nonneg_right _ (by positivity) <;> linarith
  have hA : 0 ≤ nu α (k+1) * Z * ∑ i, s (k+1) i := by positivity
  have hB : 0 ≤ nu α (k+1) * Z * ∑ i, x (k+1) i := by positivity
  obtain ⟨T2a, -⟩ := T2 _ _ hA hB (by nlinarith)
  obtain ⟨-, T2b⟩ := T2 _ _ hA hB (by nlinarith)
  have eK : K * q = Real.sqrt (n * (1 + 1 / γ)) * q + 2 * Z * C₁ / g * q := by rw [hK]; ring
  rw [eK]
  constructor <;> linarith [hc.1, hc.2]


section g72wy_key
open Matrix

theorem g72wy_abs_le_n2 {n : ℕ} (u : Fin n → ℝ) (i : Fin n) : |u i| ≤ norm2 u := by
  unfold norm2
  apply Real.abs_le_sqrt
  exact Finset.single_le_sum (f := fun j => u j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)

theorem g72wy_cs {n : ℕ} (u v : Fin n → ℝ) : |∑ i, u i * v i| ≤ norm2 u * norm2 v := by
  unfold norm2
  rw [← Real.sqrt_mul (Finset.sum_nonneg (fun i _ => sq_nonneg (u i)))]
  apply Real.abs_le_sqrt
  exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _

theorem g72wy_prod {n : ℕ} (x s dx ds : Fin n → ℝ) (hx : ∀ i, 0 < x i) (hs : ∀ i, 0 < s i)
    (C μ : ℝ) (hμ : 0 ≤ μ)
    (h1 : norm2 (scaledDx x s dx) ≤ C * Real.sqrt μ)
    (h2 : norm2 (scaledDs x s ds) ≤ C * Real.sqrt μ) :
    (∀ i, |dx i * ds i| ≤ C ^ 2 * μ) ∧ |∑ i, dx i * ds i| ≤ C ^ 2 * μ := by
  have he : ∀ i, dx i * ds i = scaledDx x s dx i * scaledDs x s ds i := by
    intro i
    unfold scaledDx scaledDs
    have : Real.sqrt (s i / x i) * Real.sqrt (x i / s i) = 1 := by
      rw [← Real.sqrt_mul (div_nonneg (hs i).le (hx i).le)]
      rw [div_mul_div_comm, mul_comm (s i), div_self (mul_pos (hx i) (hs i)).ne', Real.sqrt_one]
    linear_combination (-(dx i * ds i)) * this
  have hu0 : 0 ≤ norm2 (scaledDx x s dx) := Real.sqrt_nonneg _
  have hv0 : 0 ≤ norm2 (scaledDs x s ds) := Real.sqrt_nonneg _
  have hq : C * Real.sqrt μ * (C * Real.sqrt μ) = C ^ 2 * μ := by
    have := Real.sq_sqrt hμ
    linear_combination C ^ 2 * this
  have key : norm2 (scaledDx x s dx) * norm2 (scaledDs x s ds) ≤ C ^ 2 * μ := by
    rw [← hq]; exact mul_le_mul h1 h2 hv0 (hu0.trans h1)
  constructor
  · intro i
    rw [he i, abs_mul]
    refine le_trans ?_ key
    exact mul_le_mul (g72wy_abs_le_n2 _ i) (g72wy_abs_le_n2 _ i) (abs_nonneg _) hu0
  · have : ∑ i, dx i * ds i = ∑ i, scaledDx x s dx i * scaledDs x s ds i :=
      Finset.sum_congr rfl (fun i _ => he i)
    rw [this]
    exact (g72wy_cs _ _).trans key

theorem g72wy_dot_expand {n : ℕ} (x s dx ds : Fin n → ℝ) (a σ : ℝ)
    (hstep : ∀ i, s i * dx i + x i * ds i = -(x i * s i) + σ * mu x s) :
    (x + a • dx) ⬝ᵥ (s + a • ds) =
      (1 - a) * (x ⬝ᵥ s) + a * σ * (n * mu x s) + a ^ 2 * ∑ i, dx i * ds i := by
  have e1 : (x + a • dx) ⬝ᵥ (s + a • ds) = ∑ i, (x i + a * dx i) * (s i + a * ds i) := by
    simp only [dotProduct, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have e2 : ∀ i, (x i + a * dx i) * (s i + a * ds i) =
      (1 - a) * (x i * s i) + a * σ * mu x s + a ^ 2 * (dx i * ds i) := by
    intro i; linear_combination a * hstep i
  rw [e1, Finset.sum_congr rfl (fun i _ => e2 i)]
  simp only [dotProduct, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  ring

theorem g72wy_pt {n : ℕ} (x s dx ds : Fin n → ℝ) (σ σmin γ C a : ℝ) (hn : 0 < n)
    (hx : ∀ i, 0 < x i) (hs : ∀ i, 0 < s i) (hγ : 0 < γ ∧ γ < 1) (hσmin : 0 < σmin)
    (hσ : σmin ≤ σ ∧ σ ≤ 0.5)
    (hstep : ∀ i, s i * dx i + x i * ds i = -(x i * s i) + σ * mu x s)
    (hcen : ∀ i, γ * mu x s ≤ x i * s i)
    (hb1 : norm2 (scaledDx x s dx) ≤ C * Real.sqrt (mu x s))
    (hb2 : norm2 (scaledDs x s ds) ≤ C * Real.sqrt (mu x s))
    (ha : 0 ≤ a) (haa : a * (C ^ 2 + 1) ≤ σmin * (1 - γ) / 4) :
    (x + a • dx) ⬝ᵥ (s + a • ds) ≥ (1 - a) * (x ⬝ᵥ s) ∧
    (∀ i, (x i + a * dx i) * (s i + a * ds i) ≥ (γ / n) * ((x + a • dx) ⬝ᵥ (s + a • ds))) ∧
    (x + a • dx) ⬝ᵥ (s + a • ds) ≤ (1 - 0.01 * a) * (x ⬝ᵥ s) := by
  set μ := mu x s with hμdef
  have hnr : (0:ℝ) < n := by exact_mod_cast hn
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hxs : x ⬝ᵥ s = n * μ := by rw [hμdef]; unfold mu; field_simp
  have hμ : 0 < μ := by
    rw [hμdef]; unfold mu
    apply div_pos _ hnr
    unfold dotProduct
    exact Finset.sum_pos (fun i _ => mul_pos (hx i) (hs i)) ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  obtain ⟨hpi, hP⟩ := g72wy_prod x s dx ds hx hs C μ hμ.le hb1 hb2
  set P := ∑ i, dx i * ds i with hPdef
  have hQ := g72wy_dot_expand x s dx ds a σ hstep
  rw [← hμdef] at hQ
  set Q := (x + a • dx) ⬝ᵥ (s + a • ds) with hQdef
  have hσ0 : 0 < σ := lt_of_lt_of_le hσmin hσ.1
  have hγ1 : 0 < 1 - γ := by linarith
  have hC2 : 0 ≤ C ^ 2 := sq_nonneg C
  have haC : a * C ^ 2 ≤ σmin * (1 - γ) / 4 := by
    have : a * C ^ 2 ≤ a * (C ^ 2 + 1) := by nlinarith
    linarith
  have ha4 : a ≤ 1 / 4 := by
    have : a ≤ a * (C ^ 2 + 1) := by nlinarith
    have : σmin * (1 - γ) / 4 ≤ 1 / 4 := by nlinarith
    linarith
  have hP1 : -(C ^ 2 * μ) ≤ P := by linarith [neg_abs_le P]
  have hP2 : P ≤ C ^ 2 * μ := le_trans (le_abs_self P) hP
  have haC2 : a ^ 2 * C ^ 2 ≤ a * (σ * (1 - γ) / 4) := by
    have h3 : σmin * (1 - γ) / 4 ≤ σ * (1 - γ) / 4 := by nlinarith
    have h4 := mul_le_mul_of_nonneg_left (haC.trans h3) ha
    have : a ^ 2 * C ^ 2 = a * (a * C ^ 2) := by ring
    linarith
  have hsq : 0 ≤ a ^ 2 := sq_nonneg a
  have hPa1 : a ^ 2 * (-(C ^ 2 * μ)) ≤ a ^ 2 * P := mul_le_mul_of_nonneg_left hP1 hsq
  have hPa2 : a ^ 2 * P ≤ a ^ 2 * (C ^ 2 * μ) := mul_le_mul_of_nonneg_left hP2 hsq
  have hM := mul_le_mul_of_nonneg_right haC2 hμ.le
  have haσ : 0 ≤ a * σ * (1 - γ) * μ := by positivity
  refine ⟨?_, ?_, ?_⟩
  · -- (a)
    rw [hQ, hxs]
    have h3 : a * σ * (1 - γ) * μ ≤ a * σ * (n * μ) := by
      have : (1 - γ) * μ ≤ n * μ := mul_le_mul_of_nonneg_right (by linarith) hμ.le
      have h5 := mul_le_mul_of_nonneg_left this (mul_nonneg ha hσ0.le)
      linarith
    linarith
  · intro i
    have e : (x i + a * dx i) * (s i + a * ds i) =
        (1 - a) * (x i * s i) + a * σ * μ + a ^ 2 * (dx i * ds i) := by
      linear_combination a * hstep i
    rw [e, hQ, hxs]
    have hpi' : -(C ^ 2 * μ) ≤ dx i * ds i := by linarith [neg_abs_le (dx i * ds i), hpi i]
    have ha1 : 0 ≤ 1 - a := by linarith
    have l1 := mul_le_mul_of_nonneg_left (hcen i) ha1
    have l2 := mul_le_mul_of_nonneg_left hpi' hsq
    have e2 : γ / n * ((1 - a) * (n * μ) + a * σ * (n * μ) + a ^ 2 * P) =
        (1 - a) * (γ * μ) + γ * a * σ * μ + (γ / n) * (a ^ 2 * P) := by
      field_simp
    rw [e2]
    have hg : γ / n ≤ 1 := by rw [div_le_one hnr]; linarith
    have hg0 : 0 ≤ γ / n := div_nonneg hγ.1.le hnr.le
    have r1 : (γ / n) * (a ^ 2 * P) ≤ (γ / n) * (a ^ 2 * (C ^ 2 * μ)) :=
      mul_le_mul_of_nonneg_left hPa2 hg0
    have hz : 0 ≤ a ^ 2 * (C ^ 2 * μ) := by positivity
    have r2 : (γ / n) * (a ^ 2 * (C ^ 2 * μ)) ≤ 1 * (a ^ 2 * (C ^ 2 * μ)) :=
      mul_le_mul_of_nonneg_right hg hz
    have r3 : γ * (a * σ * μ) ≤ 1 * (a * σ * μ) := by
      have : 0 ≤ a * σ * μ := by positivity
      exact mul_le_mul_of_nonneg_right hγ.2.le this
    have r4 : γ * a * σ * μ = γ * (a * σ * μ) := by ring
    linarith
  · rw [hQ, hxs]
    have h3 : a * (σ * (1 - γ) / 4) * μ ≤ a * (0.99 - σ) * (n * μ) := by
      have : σ * (1 - γ) / 4 * μ ≤ (0.99 - σ) * (n * μ) := by
        have h6 : σ * (1 - γ) / 4 ≤ (0.99 - σ) * 1 := by nlinarith
        have h7 : (0.99 - σ) * 1 ≤ (0.99 - σ) * n :=
          mul_le_mul_of_nonneg_left hn1 (by norm_num at hσ ⊢; linarith)
        have := mul_le_mul_of_nonneg_right (h6.trans h7) hμ.le
        linarith
      have := mul_le_mul_of_nonneg_left this ha
      linarith
    linarith

end g72wy_key

section g72wy_key2
open Matrix

theorem g72wy_rb_step {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (x dx : Fin n → ℝ)
    (a : ℝ) (h : A *ᵥ dx = -rb A b x) : rb A b (x + a • dx) = (1 - a) • rb A b x := by
  unfold rb at *
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, h]
  ext i; simp; ring

theorem g72wy_rc_step {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (lam dlam : Fin m → ℝ)
    (s ds : Fin n → ℝ) (a : ℝ) (h : Aᵀ *ᵥ dlam + ds = -rc A c lam s) :
    rc A c (lam + a • dlam) (s + a • ds) = (1 - a) • rc A c lam s := by
  have h' : ∀ i, (Aᵀ *ᵥ dlam) i + ds i = -(rc A c lam s) i := fun i => congrFun h i
  unfold rc at *
  ext i
  have := h' i
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Pi.add_apply, Pi.smul_apply, Pi.sub_apply,
    smul_eq_mul, Pi.neg_apply] at this ⊢
  linear_combination a * this

theorem g72wy_res_step {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x : Fin n → ℝ) (lam : Fin m → ℝ) (s dx : Fin n → ℝ) (dlam : Fin m → ℝ) (ds : Fin n → ℝ)
    (a : ℝ) (ha : a ≤ 1) (h1 : Aᵀ *ᵥ dlam + ds = -rc A c lam s) (h2 : A *ᵥ dx = -rb A b x) :
    resNorm A b c (x + a • dx) (lam + a • dlam) (s + a • ds) = (1 - a) * resNorm A b c x lam s := by
  unfold resNorm
  rw [g72wy_rb_step A b x dx a h2, g72wy_rc_step A c lam dlam s ds a h1]
  have e : ∑ i, ((1 - a) • rb A b x) i ^ 2 + ∑ j, ((1 - a) • rc A c lam s) j ^ 2 =
      (1 - a) ^ 2 * (∑ i, rb A b x i ^ 2 + ∑ j, rc A c lam s j ^ 2) := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_pow, mul_add, Finset.mul_sum]
  rw [e, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by linarith)]

theorem g72wy_key2 {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ} {c : Fin n → ℝ}
    {γ β σmin σmax : ℝ}
    {x : ℕ → Fin n → ℝ} {lam : ℕ → Fin m → ℝ} {s : ℕ → Fin n → ℝ} {σ α : ℕ → ℝ}
    {dx : ℕ → Fin n → ℝ} {dlam : ℕ → Fin m → ℝ} {ds : ℕ → Fin n → ℝ}
    (hrun : IsIPFIterates A b c γ β σmin σmax x lam s σ α dx dlam ds)
    (hγ : 0 < γ ∧ γ < 1) (hβ : 1 ≤ β) (hσ : 0 < σmin ∧ σmin < σmax ∧ σmax ≤ 0.5) (hn : 0 < n)
    (k : ℕ) (hNk : (x k, lam k, s k) ∈ NegInfNbhd A b c γ β (x 0) (lam 0) (s 0))
    (C : ℝ) (hb : ∀ k, norm2 (scaledDx (x k) (s k) (dx k)) ≤ C * Real.sqrt (mu (x k) (s k)) ∧
      norm2 (scaledDs (x k) (s k) (ds k)) ≤ C * Real.sqrt (mu (x k) (s k)))
    (a : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) (σmin * (1 - γ) / (4 * (C ^ 2 + 1)))) :
        (x k + a • dx k) ⬝ᵥ (s k + a • ds k) ≥ (1 - a) * (x k ⬝ᵥ s k) ∧
        (∀ i, (x k i + a * dx k i) * (s k i + a * ds k i) ≥
          (γ / n) * ((x k + a • dx k) ⬝ᵥ (s k + a • ds k))) ∧
        (x k + a • dx k) ⬝ᵥ (s k + a • ds k) ≤ (1 - 0.01 * a) * (x k ⬝ᵥ s k) ∧
        (x k + a • dx k, lam k + a • dlam k, s k + a • ds k) ∈
          NegInfNbhd A b c γ β (x 0) (lam 0) (s 0) ∧
        mu (x k + a • dx k) (s k + a • ds k) ≤ (1 - 0.01 * a) * mu (x k) (s k) := by
  have hnr : (0:ℝ) < n := by exact_mod_cast hn
  have hC1 : 0 < 4 * (C ^ 2 + 1) := by positivity
  have hxk := hNk.2.1
  have hsk := hNk.2.2.1
  have hσk := hrun.sigma_mem k
  have hstep := hrun.step k
  have hxs0 : 0 < x k ⬝ᵥ s k := by
    unfold dotProduct
    exact Finset.sum_pos (fun i _ => mul_pos (hxk i) (hsk i)) ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have hγ1 : 0 < 1 - γ := by linarith
  have hthr : σmin * (1 - γ) / 4 ≤ 1 / 4 := by nlinarith
  have pt : ∀ t, 0 ≤ t → t ≤ a →
      (x k + t • dx k) ⬝ᵥ (s k + t • ds k) ≥ (1 - t) * (x k ⬝ᵥ s k) ∧
      (∀ i, (x k i + t * dx k i) * (s k i + t * ds k i) ≥
        (γ / n) * ((x k + t • dx k) ⬝ᵥ (s k + t • ds k))) ∧
      (x k + t • dx k) ⬝ᵥ (s k + t • ds k) ≤ (1 - 0.01 * t) * (x k ⬝ᵥ s k) ∧
      t ≤ 1 / 4 := by
    intro t ht0 hta
    have htt : t * (C ^ 2 + 1) ≤ σmin * (1 - γ) / 4 := by
      have h1 : t ≤ σmin * (1 - γ) / (4 * (C ^ 2 + 1)) := hta.trans ha.2
      rw [le_div_iff₀ hC1] at h1
      linarith
    have ht4 : t ≤ 1 / 4 := by
      have : t ≤ t * (C ^ 2 + 1) := by nlinarith [sq_nonneg C]
      linarith
    obtain ⟨p1, p2, p3⟩ := g72wy_pt (x k) (s k) (dx k) (ds k) (σ k) σmin γ C t hn hxk hsk hγ hσ.1
      ⟨hσk.1, hσk.2.trans hσ.2.2⟩ hstep.2.2 hNk.2.2.2 (hb k).1 (hb k).2 ht0 htt
    exact ⟨p1, p2, p3, ht4⟩
  obtain ⟨q1, q2, q3, qa⟩ := pt a ha.1 le_rfl
  have hQpos : ∀ t, 0 ≤ t → t ≤ a → 0 < (x k + t • dx k) ⬝ᵥ (s k + t • ds k) := by
    intro t ht0 hta
    obtain ⟨r1, -, -, r4⟩ := pt t ht0 hta
    have : 0 < (1 - t) * (x k ⬝ᵥ s k) := mul_pos (by linarith) hxs0
    linarith
  have hgn : 0 < γ / n := div_pos hγ.1 hnr
  have xpos : ∀ i, 0 < x k i + a * dx k i := by
    intro i
    by_contra hc
    push_neg at hc
    have hd : dx k i < 0 := by
      by_contra hd; push_neg at hd
      have := mul_nonneg ha.1 hd
      linarith [hxk i]
    set t0 := x k i / (-dx k i) with ht0
    have hd' : 0 < -dx k i := by linarith
    have ht0p : 0 < t0 := div_pos (hxk i) hd'
    have ht0a : t0 ≤ a := by
      rw [ht0, div_le_iff₀ hd']; linarith
    have hz : x k i + t0 * dx k i = 0 := by
      rw [ht0, div_mul_eq_mul_div, div_neg, mul_div_assoc, div_self hd.ne]; ring
    obtain ⟨-, r2, -, -⟩ := pt t0 ht0p.le ht0a
    have := r2 i
    rw [hz, zero_mul] at this
    have := mul_pos hgn (hQpos t0 ht0p.le ht0a)
    linarith
  have spos : ∀ i, 0 < s k i + a * ds k i := by
    intro i
    by_contra hc
    push_neg at hc
    have hd : ds k i < 0 := by
      by_contra hd; push_neg at hd
      have := mul_nonneg ha.1 hd
      linarith [hsk i]
    set t0 := s k i / (-ds k i) with ht0
    have hd' : 0 < -ds k i := by linarith
    have ht0p : 0 < t0 := div_pos (hsk i) hd'
    have ht0a : t0 ≤ a := by
      rw [ht0, div_le_iff₀ hd']; linarith
    have hz : s k i + t0 * ds k i = 0 := by
      rw [ht0, div_mul_eq_mul_div, div_neg, mul_div_assoc, div_self hd.ne]; ring
    obtain ⟨-, r2, -, -⟩ := pt t0 ht0p.le ht0a
    have := r2 i
    rw [hz, mul_zero] at this
    have := mul_pos hgn (hQpos t0 ht0p.le ht0a)
    linarith
  have hmuA : mu (x k + a • dx k) (s k + a • ds k) = (x k + a • dx k) ⬝ᵥ (s k + a • ds k) / n := rfl
  have hmuk : mu (x k) (s k) = x k ⬝ᵥ s k / n := rfl
  refine ⟨q1, q2, q3, ?_, ?_⟩
  · simp only [NegInfNbhd, Set.mem_setOf_eq]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [g72wy_res_step A b c (x k) (lam k) (s k) (dx k) (dlam k) (ds k) a (by linarith)
        hstep.1 hstep.2.1]
      have hk := hNk.1
      simp only at hk
      set K := resNorm A b c (x 0) (lam 0) (s 0) / mu (x 0) (s 0) * β with hK
      have hK0 : 0 ≤ K := by
        have hm0 : 0 ≤ mu (x 0) (s 0) := by
          unfold mu dotProduct
          exact div_nonneg (Finset.sum_nonneg (fun i _ => (mul_pos (hrun.start_pos.1 i)
            (hrun.start_pos.2 i)).le)) hnr.le
        have : 0 ≤ resNorm A b c (x 0) (lam 0) (s 0) := Real.sqrt_nonneg _
        positivity
      have e1 : (1 - a) * resNorm A b c (x k) (lam k) (s k) ≤ (1 - a) * (K * mu (x k) (s k)) :=
        mul_le_mul_of_nonneg_left hk (by linarith)
      have e2 : (1 - a) * mu (x k) (s k) ≤ mu (x k + a • dx k) (s k + a • ds k) := by
        rw [hmuA, hmuk, mul_div_assoc']
        exact div_le_div_of_nonneg_right q1 hnr.le
      have e3 := mul_le_mul_of_nonneg_left e2 hK0
      linarith
    · intro i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; exact xpos i
    · intro i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; exact spos i
    · intro i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [hmuA]
      have := q2 i
      have e : γ * ((x k + a • dx k) ⬝ᵥ (s k + a • ds k) / n) =
          γ / n * ((x k + a • dx k) ⬝ᵥ (s k + a • ds k)) := by ring
      linarith
  · rw [hmuA, hmuk, mul_div_assoc']
    exact div_le_div_of_nonneg_right q3 hnr.le

end g72wy_key2

section g72wy_gtdefs
open Matrix
def g72wy_PF {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (x : Fin n → ℝ) : Prop :=
  A *ᵥ x = b ∧ ∀ j, 0 ≤ x j
def g72wy_DF {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ)
    (lam : Fin m → ℝ) (s : Fin n → ℝ) : Prop :=
  Aᵀ *ᵥ lam + s = c ∧ ∀ j, 0 ≤ s j
def g72wy_OP {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) :
    Set (Fin n → ℝ) :=
  {x | g72wy_PF A b x ∧ ∀ x', g72wy_PF A b x' → c ⬝ᵥ x ≤ c ⬝ᵥ x'}
def g72wy_OD {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) :
    Set ((Fin m → ℝ) × (Fin n → ℝ)) :=
  {p | g72wy_DF A c p.1 p.2 ∧
    ∀ lam' s', g72wy_DF A c lam' s' → b ⬝ᵥ lam' ≤ b ⬝ᵥ p.1}
def g72wy_Om {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) :
    Set ((Fin n → ℝ) × (Fin m → ℝ) × (Fin n → ℝ)) :=
  {p | p.1 ∈ g72wy_OP A b c ∧ (p.2.1, p.2.2) ∈ g72wy_OD A b c}
def g72wy_iB {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) :
    Set (Fin n) :=
  {j | ∃ x ∈ g72wy_OP A b c, x j ≠ 0}
def g72wy_iN {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) :
    Set (Fin n) :=
  {j | ∃ p ∈ g72wy_OD A b c, p.2 j ≠ 0}
end g72wy_gtdefs

section g72wy_gtsec
open Matrix
theorem g69a1_cara {ι E : Type*} [DecidableEq ι] [AddCommGroup E] [Module ℝ E] (v : ι → E)
    (t : Finset ι) : ∀ l : ι → ℝ, (∀ i, 0 ≤ l i) → ∃ s ⊆ t, ∃ l' : ι → ℝ, (∀ i, 0 ≤ l' i) ∧
      LinearIndepOn ℝ v (s : Set ι) ∧ ∑ i ∈ s, l' i • v i = ∑ i ∈ t, l i • v i := by
  induction t using Finset.strongInduction with
  | H t ih =>
  intro l hl
  by_cases hli : LinearIndepOn ℝ v (t : Set ι)
  · exact ⟨t, subset_rfl, l, hl, hli, rfl⟩
  rw [not_linearIndepOn_finset_iffₛ] at hli
  obtain ⟨f, g, hfg, i0, hi0t, hi0⟩ := hli
  have hsum0 : ∑ i ∈ t, (f i - g i) • v i = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, hfg, sub_self]
  -- get ν supported on t with positive entry
  obtain ⟨ν, hνsum, hνsupp, i1, hi1t, hi1⟩ : ∃ ν : ι → ℝ, ∑ i ∈ t, ν i • v i = 0 ∧
      (∀ i, i ∉ t → ν i = 0) ∧ ∃ i ∈ t, 0 < ν i := by
    rcases lt_or_gt_of_ne (sub_ne_zero.mpr hi0) with h | h
    · refine ⟨fun i => if i ∈ t then -(f i - g i) else 0, ?_, ?_, i0, hi0t, ?_⟩
      · have hc : ∀ i ∈ t, (if i ∈ t then -(f i - g i) else 0) • v i = -((f i - g i) • v i) := by
          intro i hi; rw [if_pos hi, neg_smul]
        beta_reduce
        rw [Finset.sum_congr rfl hc, Finset.sum_neg_distrib, hsum0, neg_zero]
      · intro i hi; simp [hi]
      · simp only [hi0t, if_true]; linarith
    · refine ⟨fun i => if i ∈ t then (f i - g i) else 0, ?_, ?_, i0, hi0t, ?_⟩
      · have hc : ∀ i ∈ t, (if i ∈ t then (f i - g i) else 0) • v i = (f i - g i) • v i := by
          intro i hi; rw [if_pos hi]
        beta_reduce
        rw [Finset.sum_congr rfl hc, hsum0]
      · intro i hi; simp [hi]
      · simp only [hi0t, if_true]; linarith
  set P := t.filter (fun i => 0 < ν i) with hP
  have hPne : P.Nonempty := ⟨i1, by simp [hP, hi1t, hi1]⟩
  obtain ⟨j, hjP, hjmin⟩ := Finset.exists_min_image P (fun i => l i / ν i) hPne
  have hjt : j ∈ t := (Finset.mem_filter.mp hjP).1
  have hjpos : 0 < ν j := (Finset.mem_filter.mp hjP).2
  set θ := l j / ν j with hθ
  have hθnn : 0 ≤ θ := div_nonneg (hl j) hjpos.le
  set l' : ι → ℝ := fun i => l i - θ * ν i with hl'
  have hl'nn : ∀ i, 0 ≤ l' i := by
    intro i
    simp only [hl']
    by_cases hit : i ∈ t
    · by_cases hνi : 0 < ν i
      · have hiP : i ∈ P := by simp [hP, hit, hνi]
        have := hjmin i hiP
        rw [le_div_iff₀ hνi] at this
        linarith
      · push Not at hνi
        nlinarith [hl i]
    · rw [hνsupp i hit]; simp [hl i]
  have hl'j : l' j = 0 := by
    simp only [hl', hθ]; field_simp; ring
  have hsum' : ∑ i ∈ t.erase j, l' i • v i = ∑ i ∈ t, l i • v i := by
    rw [Finset.sum_erase _ (by rw [hl'j, zero_smul])]
    simp only [hl', sub_smul, Finset.sum_sub_distrib, mul_smul, ← Finset.smul_sum, hνsum,
      smul_zero, sub_zero]
  obtain ⟨s, hs, l'', hl'', hli, hs'⟩ := ih (t.erase j) (Finset.erase_ssubset hjt) l' hl'nn
  exact ⟨s, hs.trans (Finset.erase_subset _ _), l'', hl'', hli, hs'.trans hsum'⟩

theorem g69a1_cone_closed {ι : Type*} [Fintype ι] {κ : Type*} [Fintype κ] (v : ι → κ → ℝ) :
    IsClosed {y : κ → ℝ | ∃ l : ι → ℝ, (∀ i, 0 ≤ l i) ∧ y = ∑ i, l i • v i} := by
  classical
  have heq : {y : κ → ℝ | ∃ l : ι → ℝ, (∀ i, 0 ≤ l i) ∧ y = ∑ i, l i • v i} =
      ⋃ s ∈ {s : Finset ι | LinearIndepOn ℝ v (s : Set ι)},
        (Fintype.linearCombination ℝ (fun i : (s : Set ι) => v i)) '' {m | ∀ i, 0 ≤ m i} := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_image, exists_prop]
    constructor
    · rintro ⟨l, hl, rfl⟩
      obtain ⟨s, -, l', hl', hli, hs⟩ := g69a1_cara v Finset.univ l hl
      refine ⟨s, hli, fun i => l' i, fun i => hl' i, ?_⟩
      rw [Fintype.linearCombination_apply, ← hs]
      exact (Finset.sum_coe_sort s (fun i => l' i • v i))
    · rintro ⟨s, -, m, hm, rfl⟩
      refine ⟨fun i => if h : i ∈ s then m ⟨i, h⟩ else 0, ?_, ?_⟩
      · intro i; by_cases h : i ∈ s <;> simp [h, hm]
      · rw [Fintype.linearCombination_apply]
        rw [← Finset.sum_subset (Finset.subset_univ s)]
        · rw [← Finset.sum_coe_sort s]
          apply Finset.sum_congr rfl
          intro i _
          simp
        · intro i _ hi; simp [hi]
  rw [heq]
  apply Set.Finite.isClosed_biUnion (Set.toFinite _)
  intro s hs
  have hinj : LinearMap.ker (Fintype.linearCombination ℝ (fun i : (s : Set ι) => v i)) = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    exact (linearIndependent_iff_injective_fintypeLinearCombination).mp hs
  apply (LinearMap.isClosedEmbedding_of_injective hinj).isClosedMap
  rw [Set.setOf_forall]
  exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)

theorem g69a1_farkas {ι : Type*} [Fintype ι] {κ : Type*} [Fintype κ] [DecidableEq κ]
    (v : ι → κ → ℝ) (a : κ → ℝ)
    (ha : ¬ ∃ l : ι → ℝ, (∀ i, 0 ≤ l i) ∧ a = ∑ i, l i • v i) :
    ∃ x : κ → ℝ, a ⬝ᵥ x < 0 ∧ ∀ i, 0 ≤ v i ⬝ᵥ x := by
  classical
  set C := {y : κ → ℝ | ∃ l : ι → ℝ, (∀ i, 0 ≤ l i) ∧ y = ∑ i, l i • v i} with hC
  have hconv : Convex ℝ C := by
    rintro y ⟨l, hl, rfl⟩ z ⟨m, hm, rfl⟩ α β hα hβ _
    refine ⟨fun i => α * l i + β * m i, fun i => by have := hl i; have := hm i; positivity, ?_⟩
    simp only [Finset.smul_sum, add_smul, mul_smul, Finset.sum_add_distrib]
  obtain ⟨f, u, hfa, hfC⟩ := geometric_hahn_banach_point_closed hconv (g69a1_cone_closed v) ha
  have hu : u < 0 := by
    have := hfC 0 ⟨0, fun _ => le_rfl, by simp⟩
    simpa using this
  have hfnn : ∀ y ∈ C, 0 ≤ f y := by
    intro y hy
    by_contra hneg
    push Not at hneg
    obtain ⟨l, hl, rfl⟩ := hy
    set t : ℝ := u / f (∑ i, l i • v i) with ht
    have htpos : 0 < t := div_pos_of_neg_of_neg hu hneg
    have hmem : t • (∑ i, l i • v i) ∈ C :=
      ⟨fun i => t * l i, fun i => mul_nonneg htpos.le (hl i), by
        simp only [Finset.smul_sum, mul_smul]⟩
    have := hfC _ hmem
    rw [map_smul, smul_eq_mul, ht, div_mul_cancel₀ _ hneg.ne] at this
    exact lt_irrefl _ this
  let x : κ → ℝ := fun j => f (Pi.single j 1)
  have hfx : ∀ y : κ → ℝ, f y = y ⬝ᵥ x := by
    intro y
    conv_lhs => rw [show y = ∑ j, y j • Pi.single j (1:ℝ) by
      ext k; simp [Finset.sum_apply, Pi.single_apply]]
    simp [map_sum, dotProduct, x]
  refine ⟨x, ?_, ?_⟩
  · rw [← hfx]; linarith
  · intro i
    rw [← hfx]
    apply hfnn
    refine ⟨Pi.single i 1, fun j => ?_, ?_⟩
    · by_cases h : j = i <;> simp [Pi.single_apply, h]
    · simp [Pi.single_apply]


theorem g69a1_lp_dualG {ι κ : Type*} [Fintype ι] [Fintype κ] (A : Matrix ι κ ℝ) (b : ι → ℝ) (c : κ → ℝ)
    (hfeas : ∃ x0, b ≤ A *ᵥ x0) (a : ℝ) (hlb : ∀ x, b ≤ A *ᵥ x → a ≤ c ⬝ᵥ x) :
    ∃ y : ι → ℝ, 0 ≤ y ∧ Aᵀ *ᵥ y = c ∧ a ≤ b ⬝ᵥ y := by
  classical
  obtain ⟨x0, hx0⟩ := hfeas
  let w : Option ι → (κ ⊕ Unit → ℝ) := fun o =>
    match o with
    | none => Sum.elim 0 (fun _ => 1)
    | some i => Sum.elim (fun j => A i j) (fun _ => -b i)
  let q : κ ⊕ Unit → ℝ := Sum.elim c (fun _ => -a)
  have hno : ¬ ∃ z : κ ⊕ Unit → ℝ, q ⬝ᵥ z < 0 ∧ ∀ o, 0 ≤ w o ⬝ᵥ z := by
    rintro ⟨z, hz, hw⟩
    set x : κ → ℝ := fun j => z (Sum.inl j) with hxdef
    set t : ℝ := z (Sum.inr ()) with htdef
    have hqz : q ⬝ᵥ z = c ⬝ᵥ x - a * t := by
      simp [q, dotProduct, Fintype.sum_sum_type, x, t]; ring
    have ht0 : 0 ≤ t := by
      have := hw none
      simpa [w, dotProduct, Fintype.sum_sum_type, t] using this
    have hAx : ∀ i, b i * t ≤ (A *ᵥ x) i := by
      intro i
      have := hw (some i)
      simp [w, dotProduct, Fintype.sum_sum_type, t] at this
      simp only [mulVec, dotProduct, x]
      linarith
    rcases ht0.lt_or_eq with htpos | htz
    · have hfe : b ≤ A *ᵥ (t⁻¹ • x) := by
        intro i
        rw [mulVec_smul, Pi.smul_apply, smul_eq_mul, le_inv_mul_iff₀ htpos]
        linarith [hAx i]
      have := hlb _ hfe
      rw [dotProduct_smul, smul_eq_mul, le_inv_mul_iff₀ htpos] at this
      linarith
    · have hcx : c ⬝ᵥ x < 0 := by rw [← htz] at hqz; linarith
      have hAx0 : ∀ i, 0 ≤ (A *ᵥ x) i := by
        intro i; have := hAx i; rw [← htz] at this; simpa using this
      have hca := hlb x0 hx0
      set s : ℝ := (c ⬝ᵥ x0 - a + 1) / (-(c ⬝ᵥ x)) with hs
      have hspos : 0 ≤ s := div_nonneg (by linarith) (by linarith)
      have hfe : b ≤ A *ᵥ (x0 + s • x) := by
        intro i
        rw [mulVec_add, mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        have := hx0 i
        nlinarith [hAx0 i]
      have := hlb _ hfe
      rw [dotProduct_add, dotProduct_smul, smul_eq_mul, hs, div_mul_eq_mul_div,
        div_neg, mul_div_assoc, div_self hcx.ne, mul_one] at this
      linarith
  have hmem : ∃ l : Option ι → ℝ, (∀ o, 0 ≤ l o) ∧ q = ∑ o, l o • w o := by
    by_contra hne
    exact hno (g69a1_farkas w q hne)
  obtain ⟨l, hl, hq⟩ := hmem
  refine ⟨fun i => l (some i), fun i => hl (some i), ?_, ?_⟩
  · funext j
    have := congrFun hq (Sum.inl j)
    simp [q, w, Finset.sum_apply, Fintype.sum_option] at this
    rw [this]
    simp [mulVec, dotProduct, mul_comm]
  · have := congrFun hq (Sum.inr ())
    simp [q, w, Finset.sum_apply, Fintype.sum_option] at this
    have h1 := hl none
    simp only [dotProduct]
    have h2 : ∑ x, l (some x) * b x = ∑ x, b x * l (some x) := by
      apply Finset.sum_congr rfl; intro i _; ring
    linarith

theorem g70wr_dual {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c d : Fin n → ℝ)
    (δ a : ℝ)
    (hfeas : ∃ x0 : Fin n → ℝ, A *ᵥ x0 = b ∧ (∀ j, 0 ≤ x0 j) ∧ d ⬝ᵥ x0 ≤ δ)
    (hlb : ∀ x : Fin n → ℝ, A *ᵥ x = b → (∀ j, 0 ≤ x j) → d ⬝ᵥ x ≤ δ → a ≤ c ⬝ᵥ x) :
    ∃ (y : Fin m → ℝ) (w : Fin n → ℝ) (t : ℝ), (∀ j, 0 ≤ w j) ∧ 0 ≤ t ∧
      Aᵀ *ᵥ y + w - t • d = c ∧ a ≤ b ⬝ᵥ y - t * δ := by
  classical
  let A' : Matrix (Fin m ⊕ Fin m ⊕ Fin n ⊕ Unit) (Fin n) ℝ :=
    Matrix.of (Sum.elim (fun i j => A i j) (Sum.elim (fun i j => -A i j)
      (Sum.elim (fun i j => if i = j then 1 else 0) (fun _ j => -d j))))
  let b' : Fin m ⊕ Fin m ⊕ Fin n ⊕ Unit → ℝ :=
    Sum.elim b (Sum.elim (-b) (Sum.elim 0 (fun _ => -δ)))
  have key : ∀ x : Fin n → ℝ, b' ≤ A' *ᵥ x ↔ (A *ᵥ x = b ∧ (∀ j, 0 ≤ x j) ∧ d ⬝ᵥ x ≤ δ) := by
    intro x
    constructor
    · intro h
      refine ⟨?_, ?_, ?_⟩
      · funext i
        have h1 := h (Sum.inl i)
        have h2 := h (Sum.inr (Sum.inl i))
        simp [A', b', mulVec, dotProduct] at h1 h2
        simp only [mulVec, dotProduct]
        linarith
      · intro j
        have h1 := h (Sum.inr (Sum.inr (Sum.inl j)))
        simpa [A', b', mulVec, dotProduct] using h1
      · have h1 := h (Sum.inr (Sum.inr (Sum.inr ())))
        simp [A', b', mulVec, dotProduct] at h1
        simp only [dotProduct]
        linarith
    · rintro ⟨h1, h2, h3⟩ r
      rcases r with i | i | j | u
      · have := congrFun h1 i
        simp [A', b', mulVec, dotProduct] at this ⊢
        linarith
      · have := congrFun h1 i
        simp [A', b', mulVec, dotProduct] at this ⊢
        linarith
      · simpa [A', b', mulVec, dotProduct] using h2 j
      · simp [A', b', mulVec, dotProduct] at h3 ⊢
        linarith
  obtain ⟨x0, hx0⟩ := hfeas
  obtain ⟨Y, hY0, hYA, hYb⟩ := g69a1_lp_dualG A' b' c ⟨x0, (key x0).2 hx0⟩ a
    (fun x hx => by obtain ⟨h1, h2, h3⟩ := (key x).1 hx; exact hlb x h1 h2 h3)
  refine ⟨fun i => Y (Sum.inl i) - Y (Sum.inr (Sum.inl i)),
    fun j => Y (Sum.inr (Sum.inr (Sum.inl j))), Y (Sum.inr (Sum.inr (Sum.inr ()))),
    fun j => hY0 _, hY0 _, ?_, ?_⟩
  · funext j
    have := congrFun hYA j
    simp [A', mulVec, dotProduct, Fintype.sum_sum_type] at this
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mulVec, dotProduct,
      transpose_apply]
    rw [← this]
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring
  · simp [b', dotProduct, Fintype.sum_sum_type] at hYb
    simp only [dotProduct, mul_sub, Finset.sum_sub_distrib]
    linarith

theorem g70wr_wd {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x : Fin n → ℝ) (lam : Fin m → ℝ) (s : Fin n → ℝ) (hx : A *ᵥ x = b)
    (hd : Aᵀ *ᵥ lam + s = c) : c ⬝ᵥ x = b ⬝ᵥ lam + s ⬝ᵥ x := by
  rw [← hd, ← hx, add_dotProduct, mulVec_transpose, dotProduct_comm (A *ᵥ x) lam, dotProduct_mulVec]

theorem g70wr_nn {n : ℕ} (s x : Fin n → ℝ) (hs : ∀ j, 0 ≤ s j) (hx : ∀ j, 0 ≤ x j) :
    0 ≤ s ⬝ᵥ x := Finset.sum_nonneg fun j _ => mul_nonneg (hs j) (hx j)

/-- dual optimal → primal feasible with equal value -/
theorem g70wr_fromD {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (p : (Fin m → ℝ) × (Fin n → ℝ)) (hp : p ∈ g72wy_OD A b c) :
    ∃ x, g72wy_PF A b x ∧ c ⬝ᵥ x = b ⬝ᵥ p.1 := by
  obtain ⟨⟨hd, hs⟩, hopt⟩ := hp
  obtain ⟨x, hx0, hxA, hxb⟩ := g69a1_lp_dualG (-Aᵀ) (-c) (-b) ⟨p.1, by
      intro j; have := congrFun hd j; simp [neg_mulVec] at this ⊢; linarith [hs j]⟩ (-(b ⬝ᵥ p.1))
    (fun lam hl => by
      have := hopt lam (c - Aᵀ *ᵥ lam) ⟨by abel, fun j => by
        have := hl j; simp [neg_mulVec] at this ⊢; linarith⟩
      simp; linarith)
  have hAx : A *ᵥ x = b := by
    have : -(A *ᵥ x) = -b := by simpa [transpose_neg, neg_mulVec] using hxA
    exact neg_inj.mp this
  refine ⟨x, ⟨hAx, fun j => hx0 j⟩, ?_⟩
  have hw := g70wr_wd A b c x p.1 p.2 hAx hd
  have := g70wr_nn p.2 x hs (fun j => hx0 j)
  simp at hxb
  linarith

/-- primal optimal → dual feasible with equal value -/
theorem g70wr_fromP {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x : Fin n → ℝ) (hx : x ∈ g72wy_OP A b c) :
    ∃ lam s, g72wy_DF A c lam s ∧ c ⬝ᵥ x = b ⬝ᵥ lam := by
  obtain ⟨⟨hA, hx0⟩, hopt⟩ := hx
  obtain ⟨y, w, t, hw, ht, hy, hyb⟩ := g70wr_dual A b c 0 0 (c ⬝ᵥ x) ⟨x, hA, hx0, by simp⟩
    (fun x' h1 h2 _ => hopt x' ⟨h1, h2⟩)
  refine ⟨y, w, ⟨by simpa using hy, hw⟩, ?_⟩
  have hd : Aᵀ *ᵥ y + w = c := by simpa using hy
  have := g70wr_wd A b c x y w hA hd
  have := g70wr_nn w x hw hx0
  simp at hyb
  linarith

theorem g70wr_PD {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x : Fin n → ℝ) (hx : x ∈ g72wy_OP A b c) (p : (Fin m → ℝ) × (Fin n → ℝ))
    (hp : p ∈ g72wy_OD A b c) : c ⬝ᵥ x = b ⬝ᵥ p.1 := by
  obtain ⟨lam, s, ⟨hd, hs⟩, hv⟩ := g70wr_fromP A b c x hx
  have h1 := hp.2 lam s ⟨hd, hs⟩
  have h2 := g70wr_wd A b c x p.1 p.2 hx.1.1 hp.1.1
  have h3 := g70wr_nn p.2 x hp.1.2 hx.1.2
  linarith

/-- Goldman–Tucker, one index. -/
theorem g70wr_gtj {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (xs : Fin n → ℝ) (hxs : xs ∈ g72wy_OP A b c) (ps : (Fin m → ℝ) × (Fin n → ℝ))
    (hps : ps ∈ g72wy_OD A b c) (j : Fin n) :
    ∃ x ∈ g72wy_OP A b c, ∃ p ∈ g72wy_OD A b c, 0 < x j + p.2 j := by
  classical
  by_cases h : ∃ x ∈ g72wy_OP A b c, 0 < x j
  · obtain ⟨x, hx, hxj⟩ := h
    exact ⟨x, hx, ps, hps, by linarith [hps.1.2 j]⟩
  push Not at h
  set e : Fin n → ℝ := fun i => if i = j then -1 else 0 with he
  obtain ⟨y, w, t, hw, ht, hy, hyb⟩ := g70wr_dual A b e c (c ⬝ᵥ xs) 0
    ⟨xs, hxs.1.1, hxs.1.2, le_rfl⟩ (fun x h1 h2 h3 => by
      have hxo : x ∈ g72wy_OP A b c := ⟨⟨h1, h2⟩, fun x' hx' => le_trans h3 (hxs.2 x' hx')⟩
      have := h x hxo
      simp [he, dotProduct]
      linarith)
  have hval : c ⬝ᵥ xs = b ⬝ᵥ ps.1 := g70wr_PD A b c xs hxs ps hps
  have hcomp : ∀ i, (Aᵀ *ᵥ y) i + w i - t * c i = e i := fun i => by
    have := congrFun hy i; simpa using this
  rcases ht.lt_or_eq with htp | ht0
  · -- λ = y / t
    refine ⟨xs, hxs, (t⁻¹ • y, c - Aᵀ *ᵥ (t⁻¹ • y)), ⟨⟨add_sub_cancel _ _, fun i => ?_⟩, ?_⟩, ?_⟩
    · have := hcomp i
      have hei : e i ≤ 0 := by simp only [he]; split_ifs <;> norm_num
      simp only [Pi.sub_apply, mulVec_smul, Pi.smul_apply, smul_eq_mul]
      have : c i - t⁻¹ * (Aᵀ *ᵥ y) i = t⁻¹ * (w i - e i) := by
        field_simp; linarith
      rw [this]; exact mul_nonneg (inv_nonneg.mpr ht) (by linarith [hw i])
    · intro lam' s' hd'
      have h1 := g70wr_wd A b c xs lam' s' hxs.1.1 hd'.1
      have h2 := g70wr_nn s' xs hd'.2 hxs.1.2
      simp only [dotProduct_smul, smul_eq_mul]
      rw [le_inv_mul_iff₀ htp]
      have := mul_le_mul_of_nonneg_left (show b ⬝ᵥ lam' ≤ c ⬝ᵥ xs by linarith) ht
      linarith
    · have := hcomp j
      have hej : e j = -1 := by simp [he]
      simp only [Pi.sub_apply, mulVec_smul, Pi.smul_apply, smul_eq_mul]
      have : c j - t⁻¹ * (Aᵀ *ᵥ y) j = t⁻¹ * (w j + 1) := by
        field_simp; linarith
      rw [this]
      have := mul_pos (inv_pos.mpr htp) (show 0 < w j + 1 by linarith [hw j])
      linarith [hxs.1.2 j]
  · subst ht0
    refine ⟨xs, hxs, (ps.1 + y, ps.2 + w - e), ⟨⟨?_, fun i => ?_⟩, ?_⟩, ?_⟩
    · funext i
      have := hcomp i
      have := congrFun hps.1.1 i
      simp only [Pi.add_apply, Pi.sub_apply, mulVec_add] at *
      linarith
    · have hei : e i ≤ 0 := by simp only [he]; split_ifs <;> norm_num
      simp only [Pi.add_apply, Pi.sub_apply]
      linarith [hps.1.2 i, hw i]
    · intro lam' s' hd'
      have := hps.2 lam' s' hd'
      simp only [dotProduct_add]
      simp at hyb
      linarith
    · have hej : e j = -1 := by simp [he]
      simp only [Pi.add_apply, Pi.sub_apply, hej]
      linarith [hps.1.2 j, hw j, hxs.1.2 j]

theorem g70wr_gt {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (hΩ : (g72wy_Om A b c).Nonempty) :
    g72wy_iB A b c ∪ g72wy_iN A b c = Set.univ ∧
    ∃ x ∈ g72wy_OP A b c, ∃ p ∈ g72wy_OD A b c, ∀ j, 0 < x j + p.2 j := by
  classical
  obtain ⟨⟨xs, ls, ss⟩, hxs, hps⟩ := hΩ
  have main : ∃ x ∈ g72wy_OP A b c, ∃ p ∈ g72wy_OD A b c, ∀ j, 0 < x j + p.2 j := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; exact ⟨xs, hxs, _, hps, fun j => j.elim0⟩
    choose P hP Q hQ hPQ using g70wr_gtj A b c xs hxs (ls, ss) hps
    have hnr : (0 : ℝ) < n := by exact_mod_cast hn
    set k : ℝ := (n : ℝ)⁻¹ with hk
    have hkp : 0 < k := inv_pos.mpr hnr
    have hksum : ∀ v : ℝ, ∑ _i : Fin n, k * v = v := fun v => by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hk]
      field_simp
    refine ⟨k • ∑ i, P i, ⟨⟨?_, fun j => ?_⟩, fun x' hx' => ?_⟩,
      (k • ∑ i, (Q i).1, k • ∑ i, (Q i).2), ⟨⟨?_, fun j => ?_⟩, fun l' s' hd' => ?_⟩, fun j => ?_⟩
    · rw [mulVec_smul, mulVec_sum]
      funext r
      simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, (hP _).1.1, Finset.mul_sum]
      exact hksum (b r)
    · simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
      exact mul_nonneg hkp.le (Finset.sum_nonneg fun i _ => (hP i).1.2 j)
    · rw [dotProduct_smul, dotProduct_sum, smul_eq_mul]
      calc k * ∑ i, c ⬝ᵥ P i ≤ k * ∑ _i : Fin n, c ⬝ᵥ x' :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => (hP i).2 x' hx') hkp.le
        _ = c ⬝ᵥ x' := by rw [Finset.mul_sum]; exact hksum _
    · rw [mulVec_smul, mulVec_sum, ← smul_add, ← Finset.sum_add_distrib]
      funext r
      simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, (hQ _).1.1, Finset.mul_sum]
      exact hksum (c r)
    · simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
      exact mul_nonneg hkp.le (Finset.sum_nonneg fun i _ => (hQ i).1.2 j)
    · rw [dotProduct_smul, dotProduct_sum, smul_eq_mul]
      calc b ⬝ᵥ l' = k * ∑ _i : Fin n, b ⬝ᵥ l' := by rw [Finset.mul_sum]; exact (hksum _).symm
        _ ≤ k * ∑ i, b ⬝ᵥ (Q i).1 :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => (hQ i).2 l' s' hd') hkp.le
    · simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
      rw [← mul_add, ← Finset.sum_add_distrib]
      refine mul_pos hkp (lt_of_lt_of_le (hPQ j) ?_)
      exact Finset.single_le_sum (f := fun i => P i j + (Q i).2 j)
        (fun i _ => add_nonneg ((hP i).1.2 j) ((hQ i).1.2 j)) (Finset.mem_univ j)
  refine ⟨?_, main⟩
  obtain ⟨x, hx, p, hp, hj⟩ := main
  ext j
  simp only [Set.mem_union, Set.mem_univ, iff_true]
  by_cases hxj : x j = 0
  · right; exact ⟨p, hp, by have := hj j; rw [hxj] at this; simp at this; exact this.ne'⟩
  · left; exact ⟨x, hx, hxj⟩
end g72wy_gtsec

section g72wy_gt2
open Matrix

theorem g72wy_dot0 {n : ℕ} (s x : Fin n → ℝ) (hs : ∀ j, 0 ≤ s j) (hx : ∀ j, 0 ≤ x j)
    (h : s ⬝ᵥ x = 0) (i : Fin n) : s i * x i = 0 := by
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun j (_ : j ∈ Finset.univ) =>
    mul_nonneg (hs j) (hx j))).mp h i (Finset.mem_univ i)
  exact this

theorem g72wy_cross {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (p q : (Fin n → ℝ) × (Fin m → ℝ) × (Fin n → ℝ)) (hp : p ∈ Omega A b c) (hq : q ∈ Omega A b c)
    (i : Fin n) : q.2.2 i * p.1 i = 0 := by
  obtain ⟨hps, hpx, hpc, hpx0, hps0⟩ := hp
  obtain ⟨hqs, hqx, hqc, hqx0, hqs0⟩ := hq
  have h1 := g70wr_wd A b c p.1 q.2.1 q.2.2 hpx hqs
  have h2 := g70wr_wd A b c p.1 p.2.1 p.2.2 hpx hps
  have h3 := g70wr_wd A b c q.1 q.2.1 q.2.2 hqx hqs
  have h4 := g70wr_wd A b c q.1 p.2.1 p.2.2 hqx hps
  have z1 : p.2.2 ⬝ᵥ p.1 = 0 := by
    unfold dotProduct; exact Finset.sum_eq_zero (fun i _ => by rw [mul_comm]; exact hpc i)
  have z2 : q.2.2 ⬝ᵥ q.1 = 0 := by
    unfold dotProduct; exact Finset.sum_eq_zero (fun i _ => by rw [mul_comm]; exact hqc i)
  have n1 := g70wr_nn q.2.2 p.1 hqs0 hpx0
  have n2 := g70wr_nn p.2.2 q.1 hps0 hqx0
  exact g72wy_dot0 q.2.2 p.1 hqs0 hpx0 (by linarith) i

theorem g72wy_gt_inf {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (hΩ : (Omega A b c).Nonempty) : ∃ p ∈ Omega A b c, ∀ j, 0 < p.1 j + p.2.2 j := by
  obtain ⟨⟨xs, ls, ss⟩, hp⟩ := hΩ
  obtain ⟨hsb, hxb, hcomp, hx0, hs0⟩ := hp
  have z : ss ⬝ᵥ xs = 0 := by
    unfold dotProduct; exact Finset.sum_eq_zero (fun i _ => by rw [mul_comm]; exact hcomp i)
  have hval := g70wr_wd A b c xs ls ss hxb hsb
  have hOP : xs ∈ g72wy_OP A b c := ⟨⟨hxb, hx0⟩, fun x' hx' => by
    have := g70wr_wd A b c x' ls ss hx'.1 hsb
    have := g70wr_nn ss x' hs0 hx'.2
    linarith⟩
  have hOD : (ls, ss) ∈ g72wy_OD A b c := ⟨⟨hsb, hs0⟩, fun l' s' hd' => by
    have := g70wr_wd A b c xs l' s' hxb hd'.1
    have := g70wr_nn s' xs hd'.2 hx0
    simp only
    linarith⟩
  obtain ⟨-, x, hx, q, hq, hj⟩ := g70wr_gt A b c ⟨(xs, ls, ss), hOP, hOD⟩
  have e1 := g70wr_PD A b c x hx q hq
  have e2 := g70wr_wd A b c x q.1 q.2 hx.1.1 hq.1.1
  refine ⟨(x, q.1, q.2), ⟨hq.1.1, hx.1.1, fun i => ?_, hx.1.2, hq.1.2⟩, hj⟩
  have := g72wy_dot0 q.2 x hq.1.2 hx.1.2 (by linarith) i
  simp only; linarith [mul_comm (x i) (q.2 i)]

end g72wy_gt2

section g72wy_68
open Matrix

theorem g72wy_orth2 {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ} {c : Fin n → ℝ}
    {γ β σmin σmax : ℝ}
    {x : ℕ → Fin n → ℝ} {lam : ℕ → Fin m → ℝ} {s : ℕ → Fin n → ℝ} {σ α : ℕ → ℝ}
    {dx : ℕ → Fin n → ℝ} {dlam : ℕ → Fin m → ℝ} {ds : ℕ → Fin n → ℝ}
    (hrun : IsIPFIterates A b c γ β σmin σmax x lam s σ α dx dlam ds)
    (p : (Fin n → ℝ) × (Fin m → ℝ) × (Fin n → ℝ)) (hp : p ∈ Omega A b c) (k : ℕ) :
    (1 - nu α k) * ∑ i, (p.1 i * s k i + p.2.2 i * x k i) ≤
      nu α k * ∑ i, (x 0 i * s 0 i + x 0 i * p.2.2 i + p.1 i * s 0 i) + ∑ i, x k i * s k i := by
  obtain ⟨hsb, hxb, hcomp, hxp, hsp⟩ := hp
  have horth := g71w_orth hrun k p.1 p.2.1 p.2.2 hxb hsb
  obtain ⟨hν0, hν1⟩ := g71w_nu_mem hrun k
  have hxk := (g71w_pos hrun k).1
  have hsk := (g71w_pos hrun k).2
  have hx0 := hrun.start_pos.1
  have hs0 := hrun.start_pos.2
  set ν := nu α k
  have hsum : ∑ i, ((ν * x 0 i + (1 - ν) * p.1 i - x k i) * (ν * s 0 i + (1 - ν) * p.2.2 i - s k i)) = 0 := by
    rw [← horth]; unfold dotProduct; rfl
  have h1 : ∀ i, (1 - ν) * (p.1 i * s k i + p.2.2 i * x k i) ≤
      ν * (x 0 i * s 0 i + x 0 i * p.2.2 i + p.1 i * s 0 i) + x k i * s k i
      - ((ν * x 0 i + (1 - ν) * p.1 i - x k i) * (ν * s 0 i + (1 - ν) * p.2.2 i - s k i)) := by
    intro i
    have e : (ν * x 0 i + (1 - ν) * p.1 i - x k i) * (ν * s 0 i + (1 - ν) * p.2.2 i - s k i)
        = ν^2 * (x 0 i * s 0 i) + ν * (1 - ν) * (x 0 i * p.2.2 i + p.1 i * s 0 i)
          + (1-ν)^2 * (p.1 i * p.2.2 i)
          - ν * (s 0 i * x k i + x 0 i * s k i) - (1 - ν) * (p.1 i * s k i + p.2.2 i * x k i)
          + x k i * s k i := by ring
    rw [e, hcomp i]
    have t1 : 0 ≤ ν * (1 - ν) * (x 0 i * s 0 i) :=
      mul_nonneg (mul_nonneg hν0 (by linarith)) (mul_pos (hx0 i) (hs0 i)).le
    have t2 : 0 ≤ ν ^ 2 * (x 0 i * p.2.2 i + p.1 i * s 0 i) :=
      mul_nonneg (sq_nonneg _) (add_nonneg (mul_nonneg (hx0 i).le (hsp i)) (mul_nonneg (hxp i) (hs0 i).le))
    have t3 : 0 ≤ ν * (s 0 i * x k i + x 0 i * s k i) :=
      mul_nonneg hν0 (add_nonneg (mul_pos (hs0 i) (hxk i)).le (mul_pos (hx0 i) (hsk i)).le)
    nlinarith [t1, t2, t3]
  have := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => h1 i)
  rw [Finset.sum_sub_distrib, hsum, sub_zero, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum] at this
  exact this

end g72wy_68

open Matrix in
set_option maxHeartbeats 1000000 in
/-- Theorem 6.8 (p. 121): along Algorithm IPF, with `Ω ≠ ∅` and an infeasible start, there is a
constant `C₃ > 0` such that for all `k` sufficiently large `0 < xᵢᵏ ≤ μ_k/C₃` (`i ∈ N`),
`0 < sᵢᵏ ≤ μ_k/C₃` (`i ∈ B`) (6.49), `sᵢᵏ ≥ C₃γ` (`i ∈ N`), `xᵢᵏ ≥ C₃γ` (`i ∈ B`) (6.50); and every
limit point `(x*, s*)` of `{(xᵏ, sᵏ)}` gives a strictly complementary solution `(x*, λ*, s*)`
for some `λ*`. -/
theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (γ β σmin σmax : ℝ) (hγ : 0 < γ ∧ γ < 1) (hβ : 1 ≤ β)
    (hσ : 0 < σmin ∧ σmin < σmax ∧ σmax ≤ 0.5)
    (hn : 0 < n)
    (x : ℕ → Fin n → ℝ) (lam : ℕ → Fin m → ℝ) (s : ℕ → Fin n → ℝ) (σ α : ℕ → ℝ)
    (dx : ℕ → Fin n → ℝ) (dlam : ℕ → Fin m → ℝ) (ds : ℕ → Fin n → ℝ)
    (hrun : IsIPFIterates A b c γ β σmin σmax x lam s σ α dx dlam ds)
    (hinf : (rb A b (x 0), rc A c (lam 0) (s 0)) ≠ (0, 0))
    (hΩ : (Omega A b c).Nonempty) :
    QLinearToZero (fun k => mu (x k) (s k)) ∧
    RLinearToZero (fun k => resNorm A b c (x k) (lam k) (s k)) := by
  obtain ⟨C, hC0, hC⟩ := g72wy_l65 A b c γ β σmin σmax hγ hβ hσ hn x lam s σ α dx dlam ds hrun hinf hΩ
  have hγ1 : 0 < 1 - γ := by linarith [hγ.2]
  set ab := σmin * (1 - γ) / (4 * (C ^ 2 + 1)) with hab
  have hab0 : 0 < ab := by have := hσ.1; positivity
  have hab1 : ab < 1 := by
    rw [hab, div_lt_one (by positivity)]
    nlinarith [sq_nonneg C, hσ.2.2, hσ.2.1, hγ.1, mul_pos hσ.1 hγ.1]
  have hαlb : ∀ j, ab ≤ α (j + 1) := by
    intro j
    have hNk := (g71w_alpha_mem hrun j).2.1
    obtain ⟨-, -, -, h4, h5⟩ := g72wy_key2 hrun hγ hβ hσ hn (j+1) hNk C hC ab ⟨hab0.le, le_rfl⟩
    exact (hrun.alpha_greatest (j+1)).2 ⟨⟨hab0.le, hab1.le⟩, h4, h5⟩
  have hmupos := g71w_mu_pos hrun hn
  set ρ := 1 - 0.01 * ab with hρ
  have hρ0 : 0 < ρ := by rw [hρ]; linarith
  have hρ1 : ρ < 1 := by rw [hρ]; linarith
  have hstep : ∀ j, mu (x (j+1+1)) (s (j+1+1)) ≤ ρ * mu (x (j+1)) (s (j+1)) := by
    intro j
    have h1 := (g71w_alpha_mem hrun (j+1)).2.2
    have h2 := hαlb j
    have hm := hmupos (j+1)
    have : (1 - 0.01 * α (j+1)) * mu (x (j+1)) (s (j+1)) ≤ ρ * mu (x (j+1)) (s (j+1)) := by
      apply mul_le_mul_of_nonneg_right _ hm.le; rw [hρ]; linarith
    exact h1.trans this
  have hmu_dec : ∀ j, mu (x (j+1)) (s (j+1)) ≤ ρ ^ j * mu (x 1) (s 1) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      calc mu (x (j+1+1)) (s (j+1+1)) ≤ ρ * mu (x (j+1)) (s (j+1)) := hstep j
        _ ≤ ρ * (ρ ^ j * mu (x 1) (s 1)) := mul_le_mul_of_nonneg_left ih hρ0.le
        _ = ρ ^ (j+1) * mu (x 1) (s 1) := by ring
  have hmu0 : Tendsto (fun k => mu (x k) (s k)) atTop (nhds 0) := by
    rw [← Filter.tendsto_add_atTop_iff_nat 1]
    have hg : Tendsto (fun j : ℕ => ρ ^ j * mu (x 1) (s 1)) atTop (nhds 0) := by
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0.le hρ1).mul_const (mu (x 1) (s 1))
      simpa using this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hg
      (fun j => (hmupos (j+1)).le) hmu_dec
  have hev : ∀ᶠ k in atTop, mu (x (k+1)) (s (k+1)) / mu (x k) (s k) ≤ ρ := by
    rw [Filter.eventually_atTop]
    refine ⟨1, fun k hk => ?_⟩
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [div_le_iff₀ (hmupos (j+1))]
    exact hstep j
  have hQ : QLinearToZero (fun k => mu (x k) (s k)) := ⟨hmupos, hmu0, ρ, hρ0, hρ1, hev⟩
  refine ⟨hQ, ?_⟩
  have hmu00 := hmupos 0
  have hr0 := g71w_res0_pos (A := A) (b := b) (c := c) (x := x) (lam := lam) (s := s) hinf
  set K := resNorm A b c (x 0) (lam 0) (s 0) * β / mu (x 0) (s 0) with hK
  have hK0 : 0 < K := by rw [hK]; have := hβ; positivity
  refine ⟨fun k => K * mu (x k) (s k), ?_, fun k => ⟨Real.sqrt_nonneg _, ?_⟩⟩
  · refine ⟨fun k => mul_pos hK0 (hmupos k), by simpa using hmu0.const_mul K, ρ, hρ0, hρ1, ?_⟩
    filter_upwards [hev] with k hk
    rw [mul_div_mul_left _ _ hK0.ne']
    exact hk
  · show resNorm A b c (x k) (lam k) (s k) ≤ K * mu (x k) (s k)
    rw [g71w_resNorm hrun k]
    have h := g71w_nu_mu hrun hβ hn hinf k
    rw [hK, div_mul_eq_mul_div, le_div_iff₀ hmu00]
    nlinarith [hr0]
