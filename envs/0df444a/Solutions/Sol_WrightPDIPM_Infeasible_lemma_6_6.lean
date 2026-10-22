-- Prove2me | solution 1 for WrightPDIPM.Infeasible.lemma_6_6
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T17:17:11.945311+00:00
-- url     : https://prove2.me/submissions/da882e1e-80fc-4a77-b3fa-3f17380c9342

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

set_option maxHeartbeats 1000000 in
/-- Lemma 6.6 (pp. 117–118): with the starting point (6.12)–(6.13), the bounds of Lemma 6.5 hold
with `C₂ = ωn`, where `ω = 9β/γ^{1/2}` (the constant the proof on p. 118 sets) does not depend
on `n`: `‖(Dᵏ)⁻¹Δxᵏ‖ ≤ ωnμ_k^{1/2}` and `‖DᵏΔsᵏ‖ ≤ ωnμ_k^{1/2}` for all `k`. -/
theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (γ β σmin σmax : ℝ) (hγ : 0 < γ ∧ γ < 1) (hβ : 1 ≤ β)
    (hσ : 0 < σmin ∧ σmin < σmax ∧ σmax ≤ 0.5)
    (hn : 0 < n)
    (x : ℕ → Fin n → ℝ) (lam : ℕ → Fin m → ℝ) (s : ℕ → Fin n → ℝ) (σ α : ℕ → ℝ)
    (dx : ℕ → Fin n → ℝ) (dlam : ℕ → Fin m → ℝ) (ds : ℕ → Fin n → ℝ)
    (hrun : IsIPFIterates A b c γ β σmin σmax x lam s σ α dx dlam ds)
    (hinf : (rb A b (x 0), rc A c (lam 0) (s 0)) ≠ (0, 0))
    (ζ : ℝ) (hx0 : x 0 = fun _ => ζ) (hlam0 : lam 0 = 0) (hs0 : s 0 = fun _ => ζ)
    (hζ : ∃ p ∈ Omega A b c, ∀ i, |p.1 i| ≤ ζ ∧ |p.2.2 i| ≤ ζ) :
    ∀ k,
      norm2 (scaledDx (x k) (s k) (dx k)) ≤
        (9 * β / Real.sqrt γ) * n * Real.sqrt (mu (x k) (s k)) ∧
      norm2 (scaledDs (x k) (s k) (ds k)) ≤
        (9 * β / Real.sqrt γ) * n * Real.sqrt (mu (x k) (s k)) := by
  have hζ0 : 0 < ζ := by have := hrun.start_pos.1 ⟨0, hn⟩; rwa [hx0] at this
  have hnr : (0:ℝ) < n := by exact_mod_cast hn
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hmu0 : mu (x 0) (s 0) = ζ ^ 2 := by
    rw [hx0, hs0]; unfold mu; simp [dotProduct]; field_simp
  have hcen : ∀ k, ∀ i, γ * mu (x k) (s k) ≤ x k i * s k i := by
    intro k
    cases k with
    | zero =>
      intro i; rw [hmu0]; rw [hx0, hs0]; nlinarith [hγ.2, sq_nonneg ζ]
    | succ k => exact g71w_cen hrun k
  intro k
  obtain ⟨p, hp, hpb⟩ := hζ
  have ⟨hsb, hxb, _, hxp, hsp⟩ := hp
  have hmu := g71w_mu_pos hrun hn k
  obtain ⟨hν0, hν1⟩ := g71w_nu_mem hrun k
  have hsumk : ∑ i, x k i * s k i = n * mu (x k) (s k) := by
    unfold mu; field_simp; rfl
  have horth := g71w_step_orth hrun k p.1 p.2.1 p.2.2 hxb hsb
  have hσk := hrun.sigma_mem k
  have hσ0 : 0 ≤ σ k := le_trans hσ.1.le hσk.1
  have hσ5 : σ k ≤ 0.5 := le_trans hσk.2 hσ.2.2
  have hz : ∀ i, |x 0 i - p.1 i| ≤ ζ := fun i => by
    rw [hx0]; have := (abs_le.mp (hpb i).1).2; have := hxp i
    rw [abs_le]; constructor <;> linarith
  have hz' : ∀ i, |s 0 i - p.2.2 i| ≤ ζ := fun i => by
    rw [hs0]; have := (abs_le.mp (hpb i).2).2; have := hsp i
    rw [abs_le]; constructor <;> linarith
  have hc := g71w_core (x k) (s k) (dx k) (ds k) (fun i => x 0 i - p.1 i) (fun i => s 0 i - p.2.2 i)
    (nu α k) (σ k) (mu (x k) (s k)) γ ζ (g71w_pos hrun k).1 (g71w_pos hrun k).2 hmu hγ.1 hν0 hσ0
    hζ0.le (hcen k) hsumk (hrun.step k).2.2 horth hz hz'
  -- key estimate
  have hm := g71w_main2 hrun p hp k
  have hnm := g71w_nu_mu hrun hβ hn hinf k
  rw [hmu0] at hnm
  rw [hx0, hs0] at hm
  simp only at hm
  have hS : ∑ i, (nu α k ^ 2 * (ζ * ζ) + nu α k * (1 - nu α k) * (ζ * p.2.2 i + p.1 i * ζ)) ≤
      ∑ _i : Fin n, 2 * nu α k * ζ ^ 2 := by
    refine Finset.sum_le_sum (fun i _ => ?_)
    have h1 := (abs_le.mp (hpb i).1).2
    have h2 := (abs_le.mp (hpb i).2).2
    have : ζ * p.2.2 i + p.1 i * ζ ≤ 2 * ζ ^ 2 := by nlinarith
    have hq : 0 ≤ nu α k * (1 - nu α k) := mul_nonneg hν0 (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left this hq]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hS
  have hsplit : ∑ i, (ζ * x k i + ζ * s k i) = ζ * (∑ i, x k i + ∑ i, s k i) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, mul_add]
  rw [hsplit, hsumk] at hm
  have hkey : nu α k * ζ * (∑ i, x k i + ∑ i, s k i) ≤ (2 * β + 1) * n * mu (x k) (s k) := by
    have : (n:ℝ) * (2 * nu α k * ζ ^ 2) ≤ 2 * n * (β * mu (x k) (s k)) := by nlinarith
    nlinarith
  have hsX : 0 ≤ ∑ i, x k i := Finset.sum_nonneg (fun i _ => ((g71w_pos hrun k).1 i).le)
  have hsS : 0 ≤ ∑ i, s k i := Finset.sum_nonneg (fun i _ => ((g71w_pos hrun k).2 i).le)
  set q := Real.sqrt (mu (x k) (s k)) with hq
  set g := Real.sqrt γ with hg
  have hq0 : 0 < q := Real.sqrt_pos.mpr hmu
  have hg0 : 0 < g := Real.sqrt_pos.mpr hγ.1
  have hqq : q ^ 2 = mu (x k) (s k) := Real.sq_sqrt hmu.le
  have hgg : g ^ 2 = γ := Real.sq_sqrt hγ.1.le
  have hgq : Real.sqrt (γ * mu (x k) (s k)) = g * q := Real.sqrt_mul hγ.1.le _
  rw [hgq] at hc
  have T1 : Real.sqrt (n * (1 + σ k ^ 2 / γ) * mu (x k) (s k)) ≤ 1.25 * n * q / g := by
    rw [← Real.sqrt_sq (show 0 ≤ 1.25 * n * q / g by positivity)]
    apply Real.sqrt_le_sqrt
    rw [div_pow, mul_pow, mul_pow, hqq, hgg, le_div_iff₀ hγ.1]
    have : (n:ℝ) * (1 + σ k ^ 2 / γ) * mu (x k) (s k) * γ = n * mu (x k) (s k) * (γ + σ k ^ 2) := by
      have hγne : γ ≠ 0 := hγ.1.ne'
      field_simp
    rw [this]
    have h1 : γ + σ k ^ 2 ≤ 1.5625 * n := by nlinarith [hγ.2]
    calc (n:ℝ) * mu (x k) (s k) * (γ + σ k ^ 2) ≤ n * mu (x k) (s k) * (1.5625 * n) :=
          mul_le_mul_of_nonneg_left h1 (mul_nonneg hnr.le hmu.le)
      _ = _ := by ring
  have T2 : ∀ A B : ℝ, 0 ≤ A → 0 ≤ B → A + B ≤ nu α k * ζ * (∑ i, x k i + ∑ i, s k i) →
      (2 * A + B) / (g * q) ≤ (4 * β + 2) * n * q / g ∧ (A + 2 * B) / (g * q) ≤ (4 * β + 2) * n * q / g := by
    intro A B hA hB hAB
    have e : (4 * β + 2) * n * q / g = 2 * ((2 * β + 1) * n * mu (x k) (s k)) / (g * q) := by
      rw [← hqq]; field_simp; ring
    rw [e]
    constructor <;> apply div_le_div_of_nonneg_right _ (by positivity) <;> linarith
  have hfin : 1.25 * n * q / g + (4 * β + 2) * n * q / g ≤ 9 * β / g * n * q := by
    rw [← add_div, div_mul_eq_mul_div, div_mul_eq_mul_div]
    apply div_le_div_of_nonneg_right _ hg0.le
    have h := mul_nonneg (show (0:ℝ) ≤ 5 * β - 3.25 by linarith) (mul_pos hnr hq0).le
    linear_combination h
  have hA : 0 ≤ nu α k * ζ * ∑ i, s k i := by positivity
  have hB : 0 ≤ nu α k * ζ * ∑ i, x k i := by positivity
  obtain ⟨T2a, -⟩ := T2 _ _ hA hB (by nlinarith)
  obtain ⟨-, T2b⟩ := T2 _ _ hA hB (by nlinarith)
  have hc1 := hc.1
  have hc2 := hc.2
  rw [hq] at T1 hfin T2a T2b ⊢
  constructor
  · linarith
  · linarith

