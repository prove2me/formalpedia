-- Prove2me | solution 1 for WrightPDIPM.Infeasible.lemma_6_3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T16:45:30.077179+00:00
-- url     : https://prove2.me/submissions/c9ffbe00-5025-4c0d-91f6-342e4c3a4bf4

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

/-- Lemma 6.3 (p. 113): along Algorithm IPF, with `Ω ≠ ∅` and an infeasible start, there is a
positive constant `C₁` (independent of `k`) with `ν_k ‖(xᵏ, sᵏ)‖₁ ≤ C₁ μ_k` for all `k ≥ 0`. -/
theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (γ β σmin σmax : ℝ) (hγ : 0 < γ ∧ γ < 1) (hβ : 1 ≤ β)
    (hσ : 0 < σmin ∧ σmin < σmax ∧ σmax ≤ 0.5)
    (hn : 0 < n)
    (x : ℕ → Fin n → ℝ) (lam : ℕ → Fin m → ℝ) (s : ℕ → Fin n → ℝ) (σ α : ℕ → ℝ)
    (dx : ℕ → Fin n → ℝ) (dlam : ℕ → Fin m → ℝ) (ds : ℕ → Fin n → ℝ)
    (hrun : IsIPFIterates A b c γ β σmin σmax x lam s σ α dx dlam ds)
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

